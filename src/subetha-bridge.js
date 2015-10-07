/*jshint -W056 */ // allow "bad constructor"
/*jshint -W041 */ // allow comparing zero with "=="
/* jshint boss:true, eqeqeq:false, expr: true */
/* global define, require, module */
/*!
 * SubEtha-Bridge
 * http://github.com/bemson/subetha-bridge/
 *
 * Copyright 2015 Bemi Faison
 * Released under the Apache License
 */
/*
LocalStorage keys:
// store network data - all channels and peers
SubEtha Network (se-net)
{
  channelLn: [<channel>, ...],
  channels: {
    <channel>: {
      peerLn: [<peer>, ...],
      peers: {
        <guid>: {
          start: <timestamp>,
          origin: <url>
        }
      }
    }
  }
}

SubEtha Message Bus (se-msg)
{
  bid: <bridge-id>,
  type: <message-type>,
  data: {
    ... // depends on command
  }
}
*/

!function (inAMD, inCJS, localStorage, Array, Date, Math, UA, scope, undefined) {

  // dependent module initializer
  function initSubEthaBridge() {

    var

      // builtins

      doc = document,
      JSONstringify = JSON.stringify,
      JSONparse = JSON.parse,
      IDB =
        scope.indexedDB ||
        scope.mozIndexedDB ||
        scope.msIndexedDB ||
        scope.webkitIndexedDB,
      IDBKR =
        scope.IDBKeyRange ||
        scope.mozIDBKeyRange ||
        scope.msIDBKeyRange ||
        scope.webkitIDBKeyRange,
      mathRandom = Math.random,
      mathRound = Math.round,
      isArray = Array.isArray,
      hasKey = Function.prototype.call.bind(Object.prototype.hasOwnProperty),
      arraySlice = Function.prototype.call.bind(Array.prototype.slice),
      concatArrays = Function.prototype.apply.bind(Array.prototype.concat),
      objectKeys = Object.keys,
      getStorage = localStorage.getItem.bind(localStorage),
      setStorage = localStorage.setItem.bind(localStorage),
      removeStorage = localStorage.removeItem.bind(localStorage),
      now = Date.now,

      // SERVER STATES

      // uninstantiated
      STATE_INITIAL = 0,
      // waiting for initial message event
      STATE_QUEUED = 1,
      // waiting for DB connection
      STATE_PENDING = 2,
      // ready to talk with host and network
      STATE_READY = 3,
      // destroyed
      STATE_DESTROYED = 4,

      // RESPONSE CODES - these codes don't matta yet

      RSP_ALLOW = 200,
      RSP_DENIED = 403,
      RSP_ABORTED = 1,
      RSP_BAD_TO_TYPE = 3,
      RSP_BAD_TO_VALUE = 4,
      RSP_BAD_TYPE = 5,
      RSP_DUPLICATE_ID = 6,
      RSP_MISSING_CHANNEL = 7,
      RSP_MISSING_DATA = 8,
      RSP_UNKNOWN_RECIPIENTS = 9,
      RSP_UNKNOWN_SENDER = 10,
      RSP_NETWORK_ERROR = 11,

      // identification - cuz IE sux

      isIE9 = /msie\s9/i.test(UA),
      isIE10 = /msie\s1/i.test(UA),
      isIE910 = isIE9 && isIE10,
      isIE11 = !isIE910 && /trident/i.test(UA),
      isIE = isIE9 || isIE10 || isIE11,

      // protocol & security

      protocolVersion = 1,
      protocolName = 'se' + protocolVersion,

      // VARIABLE FUNCTIONS

      getBridgeKillDelayFromId,
      // method name to remove client
      removeClientFromNetwork,

      // GLOBAL/SHARED

      // global DB reference
      // shared by all instances
      DB,
      // indicates when a server can complete initialization
      sysReady = 0,
      // window-level emitter
      systemBus = new EventEmitter(),
      clientTick = 0,
      docUnloading = 0,
      bridgeIds = [],
      iePeerWarrants = {},
      messageTick = 0,
      hashIgnoreFlag = {},
      requests = new Hash(),
      serverInsts = new Hash(),
      deadBridges = new Hash(),
      emitterPrototype = {
        on: function (evt, callback) {
          var me = this;

          if (
            isFullString(evt) &&
            typeof callback === 'function'
          ) {
            if (!hasKey(me, '_evts')) {
              // init events hash
              me._evts = {};
            }
            if (!hasKey(me._evts, evt)) {
              // init event queue
              me._evts[evt] = [];
            }
            // add callback to event queue
            me._evts[evt].push(callback);
          }
          return me;
        },
        off: function (evt, callback) {
          var
            me = this,
            cbs,
            cbLn,
            argLn = arguments.length;

          if (!hasKey(me, '_evts') || !argLn) {
            // reset if clearing all events
            me._evts = {};
          } else if (
            isFullString(evt) &&
            hasKey(me._evts, evt)
          ) {
            cbs = me._evts[evt];
            if (typeof callback == 'function') {
              cbLn = cbs.length;
              // remove the last matching callback only
              while (cbLn--) {
                if (cbs[cbLn] === callback) {
                  cbs.splice(cbLn, 1);
                  break;
                }
              }
            }
            // remove event queue if no callback or none left
            if (argLn < 2 || !cbs.length) {
              delete me._evts[evt];
            }
          }

          return me;
        },
        fire: function (evtName) {
          var
            me = this,
            params,
            cbs,
            cbIdx = -1,
            callbackInvoker
          ;
          if (
            isFullString(evtName) &&
            hasKey(me, '_evts') &&
            hasKey(me._evts, evtName) &&
            (cbs = me._evts[evtName]).length
          ) {
            params = arraySlice(arguments, 1);
            if (params.length) {
              callbackInvoker = function (cb) {
                cb.apply(me, params);
              };
            } else {
              callbackInvoker = function (cb) {
                cb.call(me);
              };
            }
            for (;cb = cbs[++cbIdx];) {
              callbackInvoker(cbs[cbIdx]);
            }
          }

          return me;
        }
      },
      origin =
        location.origin ||
        location.protocol + '//' + (location.port ? location.port + ':' : '') + location.hostname,
      unsupported =
        // not in an iframe
        scope.parent === scope ||
        // no message channel
        typeof MessageChannel != 'function' ||
        // no localstorage
        typeof localStorage != 'object' ||
        // no IndexedDB
        !IDB || !IDBKR,

      // localstorage keys
      // these keys tell localStorage when a change

      // message key - when new messages exist
      msgKey = protocolName + 'm',
      // network registry of all channels and peers
      w3cRegKey = protocolName + 'r',
      // client key for w3c - when client changes occur
      w3cClientKey = protocolName + 'c',

      // local storage entry point
      // one storage listener for all Server instances
      // (there would only ever be one, of course)
      // minimally normalizes localStorage change events
      // so that Server subscriber logic can be the same
      LS = {

        // cached localstorage values
        cache: new Hash(),

        watching: 0,

        // get storage key
        get: function (key) {
          var
            cache = this.cache,
            value
          ;

          // use cache first
          if (cache.has(key)) {
            value = cache.get(key);
          } else {

             // retrieve and cache localstorage value
            value = getStorage(key);

            // if there is a localStorage key present...
            if (value !== null) {
              // save the unparsed value
              // only way to compare json strings when scanning
              value = cache.set(key, value, 1);
            }

          }
          // return parsed value
          return JSONparse(value);
        },

        has: function (key) {
          // check cache - NOT localstorage
          return this.cache.has(key);
        },

        set: function (key, value, isJSON) {
          var
            me = this,
            cache = me.cache
          ;
          if (!isJSON) {
            // make safe string
            // before adding to cache and/or LS
            value = JSONstringify(value);
          }
          // capture to cache
          cache.set(key, value);
          // set localStorage
          setStorage(key, value);
        },

        // newValue is expected to be JSON
        push: function (key, newValue, oldValue) {
          var
            me = this,
            cache = me.cache,
            parsed
          ;
          if (cache.has(key)) {
            oldValue = cache.get(key);
          } else if (oldValue != undefined) {
            oldValue = null;
          }

          try {
            parsed = JSONparse(newValue);
          } catch(e) {
            // exit if parsing fails
            return;
          }

          // capture new json value
          cache.set(key, newValue, 1);

          // notify all of updated value
          systemBus.fire('ls-update', key, parsed, oldValue);
        },

        // remove key and fire storage event
        del: function (key, announce) {
          var
            me = this,
            cache = me.cache
          ;

          // remove from LS no matter what
          removeStorage(key);
          if (cache.has(key)) {
            // remove from cache
            cache.del(key);
          }
        },

        // remove key and fire local event
        pop: function (key) {
          var me = this;
          // remove key (from cache)
          me.del(key);
          // announce deletion
          systemBus.fire('ls-delete', key);
        },

        // start watching local storage
        watch: (function () {

          var watch;

          // fork approach, based on platform

          if (isIE910) {

            _watch = function (me) {
              var scanner = me.scan.bind(me);

              // debounce storage event for 30ms
              me.onstorage = function () {
                clearTimeout(me.timer);
                me.timer = setTimeout(scanner, 30);
              };

              // listen to storage events
              bind(doc, 'storage', me.onstorage);

            };

          } else if (isIE11) {

            _watch = function (me) {

              // just start looping now
              me.onstorage = setInterval(function () {
                // scan for changes
                me.scan();
              }, 100);

            };

          } else {

            // w3c

            _watch = function (me) {

              me.onstorage = function (e) {
                var
                  key = e.key,
                  value = e.newValue
                ;
                // only observe keys that begin with this protocol
                if (!key.indexOf(protocolName)) {
                  if (value === null || value === undefined) {
                    // if this is already cached
                    if (me.cache.has(key)) {
                      // notify removed key
                      me.pop(key);
                    }
                  } else {
                    // notify updated/added key
                    me.push(key, value);
                  }
                }
              };

              bind(scope, 'storage', me.onstorage);
            };

          }

          return function watch() {
            var me = this;

            if (me.watching) {
              return;
            }
            me.watching = 1;

            // cache storage protocol keys
            me.scan();

            _watch(me);
          };
        })(),

        // stop watching local storage
        unwatch: (function () {

          var _unwatch;

          // fork unwatch approach, based on platform

          if (isIE910) {

            _unwatch = function (me) {

              clearTimeout(me.timer);

              // stop listening to document storage events
              unbind(doc, 'storage', me.onstorage);

            };

          } else if (isIE11) {

            _unwatch = function (me) {
              // just start looping now
              clearInterval(me.onstorage);
            };

          } else {

            // w3c

            _unwatch = function (me) {
              // stop listening to window storage events
              unbind(scope, 'storage', me.onstorage);
            };

          }

          return function unwatch() {
            var me = this;

            if (!me.watching) {
              return;
            }
            me.watching = 0;

            _unwatch(me);

            me.onstorage = 0;

          };

        })(),

        // reconcile storage values with cache
        // this is only used by IE, to assure the cache stays synced
        // only updates keys of this protocol
        scan: function () {
          var
            me = this,
            cache = me.cache,
            keys = objectKeys(localStorage),
            cachedKeys = mix({}, cache.items),
            ln = keys.length,
            key,
            value,
            oldValue
          ;

          // sort keys
          // this ensures changes are processed in order:
          //  1 bridges "-123" suffix
          //  2 channels "-c" suffix (followed by channel name for ie)
          //  3 messages "-m" suffix
          keys.sort();

          // with each storage key
          while (ln--) {
            key = keys[ln];
            // if this is a protocol key...
            if (!key.indexOf(protocolName)) {
              // remove from cachedKeys
              delete cachedKeys[key];
              // get value (to set)
              value = getStorage(key);
              // reset old value (in case the key is new)
              oldValue = null;
              // update new keys or changed values
              if (!cache.has(key) || value != (oldValue = cache.get(key))) {
                // announce update/addition
                me.push(key, value, oldValue);
              }
            }
          }

          // delete any remaining cached keys
          // since they were not in localstorage
          for (key in cachedKeys) {
            if (hasKey(cachedKeys, key)) {
              // announce and remove key
              me.pop(key, 1);
            }
          }

        },

        // pass-thru iterator of object keys
        each: function (fn, context) {
          return this.cache.each(
            function (value, key) {
              return fn.call(this, JSONparse(value), key);
            },
            context);
        }

      },

      // REGEXPs
      r_bridgeKey = new RegExp('^' + protocolName + 'b(.+)$'), // "se1b1323" => "1323"
      r_iePeerJoin = new RegExp('^' + protocolName + 'j(.+)-(.+)$'), // "se1j<server>-<client>" => "{}"
      r_iePeerDrop = new RegExp('^' + protocolName + 'd(.+)-(.+)$'), // "se1d<server>-<client>" => ""
      r_ieChannelKey = new RegExp('^' + protocolName + 'c(.+)$'), // "se1c<client>" => "zoo"
      r_validClientRequestId = /^r\d+$/, // "r123"

      // flow control
      next =
        // use setImmediate
        (
          typeof setImmediate == 'function' &&
          setImmediate
        ) ||
        // use nextTick (for nodeJS only)
        (inCJS && process.nextTick) ||
        // fallback to slower setTimeout call
        function (fn) {
          setTimeout(fn, 0);
        },

      // dom binding utility
      bind = scope.addEventListener ?
        function (object, eventName, callback) {
          object.addEventListener(eventName, callback, false);
        } :
        function (object, eventName, callback) {
          object.attachEvent('on' + eventName, callback);
        },
      unbind = scope.removeEventListener ?
        function (object, eventName, callback) {
          object.removeEventListener(eventName, callback, false);
        } :
        function (object, eventName, callback) {
          object.detachEvent('on' + eventName, callback);
        },

      postMessageCommands = {

        // handle client authentication request
        /*
        event data structure
        {                                 [payload]
          mid: <int>,
          type: 'auth',
          data: [                         [data]
            // request object
            {
              rid: <request-id>,
              channel: <channel-name>,
              creds: [ <credential>, ... ]
            },
            ...
          ]
        }
        */
        auth: function (requests) {
          var
            server = this,
            i = 0,
            j,
            request
          ;
          // ensure we're working with an array
          if (!isArray(requests)) {
            requests = [requests];
          }
          // process each client authorization request
          for (j = requests.length; i < j; ++i) {
            // exit loop if server is killed midway
            if (server.state > STATE_READY) {
              break;
            }
            handleAuthRequest(server, requests[i]);
          }
        },

        // handle client message request
        /*
        event data structure
        {                                 [payload]
          mid: <guid>,
          type: 'msg',
          data: {                         [data]
            type: <string>,
            rid: <guid>,
            from: <guid>,
            to: [<guid>] | 0,
            data: <mixed>
          }
        }
        */
        msg: function (request) {
          var
            server = this,
            serverId = server.id,
            serverClients = server.clients,
            networkClients = server.network.clients,
            client = serverClients.get(data.from),
            clientId = client.id,
            rid = request.rid,
            recipientId = request.to,
            senderId = request.from,
            code = 0
          ;
          // exit if the request id is invalid
          if (!r_validClientRequestId.test(rid)) {
            // log error on server
            server.log('invalid request id:', rid);
            // can't respond to client without valid request id
            return;
          } else if (requests.has(rid)) {
            // log error that this request is a duplicate
            server.respond(request, RSP_DUPLICATE_ID);
            // respond to - kill other request?
            return;
          }

          // validate message

          if (!client) {
            code = RSP_UNKNOWN_SENDER;
          } else {
            // capture recipient code
            code = getRecipientCode(server, recipientId, senderId);
            // if recipients are good...
            if (!code) {
              // inspect rest of message
              if (!hasKey(request, 'data')) {
                code = RSP_MISSING_DATA;
              } else if (!isFullString(request.type)) {
                code = RSP_BAD_TYPE;
              }
            }
          }

          // add request/request type
          // this is to respond() with the proper event name
          request.type = 'request';

          // exit if any error code occurs
          if (code) {
            server.respond(request, code);
            return;
          }

          // capture send date
          request.stamp = now();

          // add message to relay queue
          server.rq.push(request);

          // run relay queue
          runRelayQueue(server);

          // add message to DB
          trans = DB.transaction('message', 'readwrite');
          trans
            .objectStore('message')
            .add({
              bid: serverId,
              channel: client.channel,
              data: request.data,
              from: clientId,
              stamp: now(),
              to: recipientId,
              type: request.type
            })
            .onsuccess = function (e) {
              // capture and return message id to host
              server.respond(request, RSP_ALLOW, e.target.result);
            }
          ;
          // handle error
          trans.onerror = function () {
            // tell host the client request failed
            server.respond(request, RSP_NETWORK_ERROR);
          };
        },

        // handle the host dropping client
        /*
        event data structure
        {                                 [payload]
          mid: <guid>,
          type: 'drop',
          data: <guid>                    [msg]
        }
        */
        drop: function (identifier) {
          var server = this;

          // identifiers beginning with "r" are request identifiers
          if (requests.has(identifier)) {

            // additional 1 removes any corresponding client
            // handles when client drops before receiving approved request
            removeAuthRequest(identifier);

          } else if (server.clients.has(identifier)) {

            dropClient(server, identifier);

          } else {
            server.log('failed drop request for', identifier);
          }

        }

      },

      // commands to handle changed and added localStorage keys
      // [0] function - the function to handle the storage event
      // [1] isString - flags when test is a regular expression or string
      // [2] challenge - the string/regxp to test the storage key
      // [3] useMatch - specifies when to use String#match instead of RegExp#test
      storageUpdateCmds = [

        // w3c & ie - read channel/client messages
        /*
          // w3c payload
          {
            bid: <int>,
            data: {
              key: <int>,       // primary-key of last message written by this bridge
              channel: <string>
            }
          }

          // ie payload - just a string
          <date>
        */
        [
          isIE ?
            // ie - simply re-read all messages
            function (server) {
              server.readMsgs();
            } :
            // w3c -  read messages up to given key for this channel
            function (server, payload) {
              var
                event = payload.data,
                channel = server.channels.get(event.channel)
              ;
              // exit if server is not known
              if (
                // unknown channel
                !channel ||
                // unknown bridge
                !server.bridges.has(value.bid)
              ) {
                return;
              }
              // capture target message key
              channel.tgtKey = event.key;
              // capture latest primary key
              server.readMsgs(channel);
            },
          // string challenge
          1,
          // "<protocol>m"
          msgKey
        ],

        // w3c & ie - addition or demise of a bridge
        /*
          // added bridge
          1<url>

          // removed bridge
          0<timestamp>
        */
        [
          function (server, payload, matches, key) {
            var
              // alias bridge id
              bid = matches[1],
              // parse bridge details from value
              bridge = hydrateBridgeFromStorageKey(bid, payload)
            ;

            // if this is a death warrant...
            if (bridge.dead) {
              // kill local bridge network now
              // schedules burial later, based on when it died
              killBridge(server, bid, bridge.died);
            } else {
              // add bridge if it does not already exist
              addBridge(server, bridge);
            }

          },
          // is regxp
          0,
          // "<protocol>b<bridge-id>"
          new RegExp('^' + protocolName + 'b(.+)$'),
          // use match
          1
        ]

      ],
      // commands to handle when a key is deleted from localStorage
      storageRemovalCmds = [
        // w3c & ie - bridge removed
        // when bridge's assets have been removed from IDB
        [
          function (server, value, matches) {
            var
              bid = matches[1],
              bridge = deadBridges.del(bid)
            ;

            // if still dead (and not buried)...
            if (bridge) {
              cancelBridgeTimer(bridge);
            }
          },
          // is regxp
          0,
          // "<protocol>b<bridge>"
          r_bridgeKey,
          // use matches
          1
        ]
      ],
      // ie storage handlers
      storageKey,

      // module definition
      Subetha = {
        // bridge version
        version: '0.0.0-alpha',
        // protocol version
        protocol: protocolName,
        // enablement flag
        supported: !unsupported,
        // expose server constructor
        Server: Server
      }
    ;

    // exit now if platform is unsupported
    if (unsupported) {
      return Subetha;
    }

    // BOOTSTRAP

    // use protocol as database name
    try {
      !function () {
        var openDB = IDB.open(protocolName, 1);

        // prep for upgrade
        openDB.onupgradeneeded = function (e) {
          var
            db = e.target.result,
            // define message table
            /*
              // message table
              {
                +id: <msg-id> db identifier
                bid: <bridge-id> db foreign key to gateway server
                channel: <string> arbitrary identifier
                data: <mixed> arbitrary message data
                from: <client-id> db foriegn key to originating client
                stamp: <number> date message was sent
                to: ( <client-id>[] | 0 ) list of recipients or none
                type: <string> arbitrary message type
              }
            */
            msgStore = db.createObjectStore(
              'message', {
                keyPath: 'id',
                autoIncrement: true
              }
            )
          ;

          msgStore.createIndex('bid', 'bid', {unique: false});
          msgStore.createIndex('from', 'from', {unique: false});
          msgStore.createIndex('channel', 'channel', {unique: false});

          /*
          clean up older databases?
            open older db
            if all bridges have expired, remove everything

          this ensures that an expired db
          doesn't take up space on device, forever
          */
        };

        // capture DB reference
        openDB.onsuccess = function (e) {
          var
            goodBridges = new Hash(),
            expiredBridges = [],
            killedBridges = {},
            timestamp = now(),
            trans,
            deadBridgeCnt,
            reqDone = 0,
            tallyDone = 0
          ;
          // capture DB globally
          DB = e.target.result;

          // capture network-related localStorage keys
          LS.scan();

          // get bridges in localStorage - synchronous call
          readBridgeKeys(
            // handle good bridge
            function (bid) {
              goodBridges.set(bid);
            },
            // handle bad bridge
            function (bid) {
              expiredBridges.push(bid);
            }
          );

          // cache count of dead bridges
          // - used for iteration purposes, either way
          reqDone =
          deadBridgeCnt =
            expiredBridges.length;

          // if there are good bridges around
          if (goodBridges.length) {
            // if there are dead bridges
            if (deadBridgeCnt) {
              // destroy each expired bridge
              while (deadBridgeCnt--) {
                // wait for all expired bridge messages to be removed
                removeBridgeEntries(expiredBridges[deadBridgeCnt], checkDone);
              }
            } else {
              // finish since there are no dead bridges
              finishInit();
            }
          } else {
            // clear tables
            trans = DB.transaction('message', 'readwrite');
            trans.objectStore('message').clear();
            trans.oncomplete = function () {
              // remove all dead bridges
              while (deadBridgeCnt--) {
                LS.del(getBridgeKeyName(expiredBridges[deadBridgeCnt]));
              }
              finishInit();
            };
          }

          // incremental check
          function checkDone() {
            if (reqDone == ++tallyDone) {
              finishInit();
            }
          }

          // complete server initialization
          function finishInit() {
            sysReady = 1;
            // tell system the system is ready
            systemBus.fire('sysRet');
            // remove all subscribers since
            // this event won't be fired again
            systemBus.off('sysRet');
          }

        };

      }();
    } catch (e) {
      // exit if the open attempt fails
      return;
    }


    // FORKS

    if (isIE) {

      // wait longest possible time based on order
      // presumes each bridge needs at least 100ms to respond
      // then, staggers additional delay based on order
      getBridgeKillDelayFromId = function (bid) {
        var totalBridgeCnt = bridgeIds.length;
        return totalBridgeCnt * 200 +
          (totalBridgeCnt - bridgeIds.indexOf(bid)) * 50;
      };

      // set ie specific storage update handlers

      // peer joined channel
      /*
        {
          channel: <int>,
          stamp: <int>
        }
      */
      storageUpdateCmds.push([
        function (server, peer, matches) {
          var
            bid = matches[1],
            pid = matches[2],
            channelName = peer.channel
          ;
          // exit when
          if (
            // bridge is this server
            server.id == bid ||
            // the joining peer has a drop flag
            LS.has(protocolName + 'd' + bid + '-' + pid) ||
            // channel not in server
            !server.channels.has(channelName) ||
            // unknown bridge
            !server.bridges.has(bid)
          ) {
            return;
          }

          // add missing members, for IDB client store
          peer.bid = bid;
          peer.id = pid;

          // add peer to server
          addPeer(server, peer);
        },
        // is regxp
        0,
        // "<protocol>j<bridge>-<client>"
        r_iePeerJoin,
        // use match
        1
      ]);

      // peer drop warrant
      // when a peer should be considered dropped
      // but before there assets have been removed from the IDB
      /*
        // scheduled peer
        1
      */
      storageUpdateCmds.push([
        function (server, isWarrant, matches, dropKey) {
          var
            bid = matches[1],
            pid = matches[2]
          ;

          // exit when...
          if (
            // bridge is this server
            server.id == bid ||
            // unknown bridge
            !server.bridges.has(bid)
          ) {
            return;
          }

          // if we don't have a warrant yet...
          if (!hasKey(iePeerWarrants, pid)) {

            // schedule clearing peer from IDB
            iePeerWarrants[pid] = setTimeout(function () {
              // delete "warrant" (timeout reference)
              ieRemovePeerWarrant(pid);

              // remove everything in IDB from this peer id
              tableDeleteEntriesOnIndex(
                // table
                'message',
                // index
                'from',
                // all from this peer
                pid,
                // callback
                function () {
                  // delete the drop key from localStorage
                  // the resulting event informs bridges you've executed this peer
                  LS.del(dropKey);
                }
              );
            }, server._delay);

          }

          // if peer exists and could be removed from this server...
          if (removePeer(server, pid)) {
            // tell host
            server.tell('drop', pid);
          }
        },
        // is regxp
        0,
        // "<protocol>d<bridge>-<client>"
        r_iePeerDrop,
        // use match
        1
      ]);

      // set ie specific storage removal handlers

      // peer drop warrant removed
      // when a peer's assets have been removed from IDB
      storageRemovalCmds.push([
        function (server, value, matches) {
          // stop scheduled peer removal
          ieRemovePeerWarrant(matches[2]);
        },
        // is regxp
        0,
        // "<protocol>d<bridge>-<client>"
        r_iePeerDrop,
        // use match
        1
      ]);

    } else {


      // wait shortest possible time, based on order
      getBridgeKillDelayFromId = function(bid) {
        return 200 + bridgeIds.indexOf(bid) * 40;
      };

      // set w3c specific storage update handlers

      // channel peer change
      // when a peer joins or drops a channel
      /*
        // "drop" payload
        {
          bid: <int>,
          type: 'drop',
          data: {
            channel: <string>,
            id: <int>
          }
        }

        // "join" payload
        {
          bid: <int>,
          type: 'join',
          data: {
            channel: <string>,
            id: <int>,
            stamp: <date>
          }
        }
      */
      storageUpdateCmds.push([
        function (server, payload) {
          var
            peer = payload.data,
            pid = peer.id,
            channelName = peer.channel,
            registry = server.reg,
            registryChannel,
            peerCnt = 0,
            isJoin  = payload.type == 'join',
            i
          ;

          // skip if bridge is unknown
          if (!server.bridges.has(payload.bid)) {
            return;
          }

          // update registry

          // if adding this peer...
          if (isJoin) {
            w3cRegisterPeer(server, channelName, pid, server.id, peer.stamp);
          } else if (hasKey(registry, channelName)) {
            // (otherwise) if dropping from known channel...
            w3cDeregisterPeer(registry, channelName, pid);
          }

          // if change is for a local, known channel...
          if (server.channels.has(channelName)) {
            // if a joining peer...
            if (isJoin) {
              // add bridge-id to peer
              peer.bid = payload.bid;
              // capture peer
              addPeer(server, peer);
            } else {
              // (otherwise) remove departing peer
              removePeer(server, peer.id);
            }

            // tell host about this peer change
            server.tell('net', payload);
          }

        },
        // string challenge
        1,
        // "<protocol>c"
        w3cClientKey
      ]);

      // set w3c specific storage removal handlers

      // removal of registry key
      // (this should never be observed)
      storageRemovalCmds.push([
        function (server) {
          server.destroy();
        },
        // is string
        1,
        // "<protocol>r"
        w3cRegKey
      ]);
    }


    // ASSIGNMENTS


    // UTILITY


    // do no harm
    function noOp() {}

    // unique enough variable length identifier
    function guish() {
      var
        max = 4,
        str = ''
      ;
      while (--max) {
        str += mathRandom().toString(26).substr(2,2);
      }
      return str;
    }

    // shallow object merge
    function mix(base) {
      var
        argIdx = 1,
        source,
        member
      ;
      for (; source = arguments[argIdx]; argIdx++) {
        for (member in source) {
          if (hasKey(source, member)) {
            base[member] = source[member];
          }
        }
      }
      return base;
    }

    function safelyParseJSON(str) {
      try {
        return JSONparse(str);
      } catch (e) {}
    }

    // quick check for non-zero length strings
    function isFullString(value) {
      return value && typeof value == 'string';
    }


    // FUNCTIONS


    // executes once DB connection has been established
    function completeServerInitialization() {
      var
        server = this,
        origin = server.origin,
        bridgesToDestroy = [],
        timestamp = now(),
        serverId,
        ln,
        serverKey,
        longestDelay,
        bridgeDeathWarrant
      ;

      // exit if already destroyed
      if (server.state > STATE_PENDING) {
        return;
      }

      // set state to ready
      server.state = STATE_READY;

      // define server id
      // multiple random chars is enough, no?
      server.id =
      serverId =
        guish();

      // define LS key
      server.key =
      serverKey =
        getBridgeKeyName(serverId);


      // add self to global server ids
      bridgeIds.push(serverId);

      // note that we're initialized
      // gives server a chance to bow out
      server.fire('init');

      // watch for localStorage changes
      // also scans storage keys
      server.rigLS();

      // resolve bridges
      readBridgeKeys(
        // good bridges
        function (bid, bridge) {
          addBridge(server, bridge);
        },
        // dead bridges
        removeBridgeEntries
      );

      // exit when...
      if (
        // server is destroyed
        server.state > STATE_READY ||
        // saving this server key fails
        !server.setKey(serverKey, '1' + origin)
      ) {
        // destroy server - if not already destroyed
        server.destroy();
        return;
      }

      try {
        // tell host we're ready to talk
        server.tell('ready', origin);
      } catch (e) {
        server.destroy();
        return;
      }

      // watch for unload event
      server.rigUnload();
      // get server delay
      updateServerDelay(server);

      // capture this instance
      serverInsts.set(serverId, server);

      // listen to host
      server.port.onmessage = handlePostMessageEvent.bind(server);

      // capture network map - w3c only (stubbed for ie)
      server.regNet();

    }

    // iterate over and return bridge objects
    function readBridgeKeys(onGoodBridge, onDeadBridge) {
      var bridges = {};

      // ensure functions may be called
      if (!onGoodBridge) {
        onGoodBridge = noOp;
      }
      if (!onDeadBridge) {
        onDeadBridge = noOp;
      }

      // retrieve all bridge keys
      LS.each(function (value, key) {
        var
          parts = key.match(r_bridgeKey),
          bridge,
          bid
        ;
        // if this is a bridge key
        if (parts) {
          // get bridge id
          bid = parts[1];
          // parse bridge status object
          bridge =
          bridges[bid] =
            hydrateBridgeFromStorageKey(bid, value);

          // invoke respective callback, based on bridge state
          if (bridge.dead) {
            onDeadBridge(bid, bridge);
          } else {
            onGoodBridge(bid, bridge);
          }
        }
      });

      // return good bridges
      return bridges;
    }

    function getBridgeKeyName(bid) {
      return protocolName + 'b' + bid;
    }

    function IDBgetEntries(tableRef, indexName, keyOnly, rangeKey, onFound, onDone) {
      // get all targeted entries from the targeted table
      var
        entries = {},
        cnt = 0,
        lastKey,
        trans,
        table,
        cursorType = 'openCursor',
        cursorProp = 'value',
        openRequest
      ;

      // if given a table name...
      if (typeof tableRef == 'string') {
        // create readonly transaction
        trans = DB.transaction(tableRef, 'readonly');
        // get table
        table = trans.objectStore(tableRef);
      } else {

        // passing a table is the only way to do a write/delete

        // use table object
        table = tableRef;
        // extract transaction
        trans = table.transaction;
      }

      // ensure that we have callbacks
      if (!onFound) {
        onFound = noOp;
      }
      if (!onDone) {
        onDone = noOp;
      }

      // refine table to point to index
      if (indexName) {
        table = table.index(indexName);
      }

      if (keyOnly) {
        // ask for keys only - faster
        cursorType = 'openKeyCursor';
        // retrieve key from cursor
        cursorProp = 'key';
      }

      // request keyed or open cursor
      if (rangeKey) {
        // resolve expected range object
        if (typeof rangeKey != 'object') {
          rangeKey = IDBKR.only(rangeKey);
        }
        openRequest = table[cursorType](rangeKey);
      } else {
        // get all records
        openRequest = table[cursorType]();
      }

      openRequest.onsuccess = function () {
        var
          lastKey,
          lastPrimaryKey,
          cursor = this.result,
          value
        ;

        // when read is complete
        if (cursor) {
          // tally entry
          ++cnt;
          // capture keys
          lastKey = cursor.key;
          lastPrimaryKey = cursor.primaryKey;

          // capture value under primary key (the cursor key can be a duplicate)
          value =
          entries[lastPrimaryKey] =
            cursor[cursorProp];

          // if the partial callback returns a truthy value
          if (onFound(value, lastKey, lastPrimaryKey, table, cnt)) {
            // stop iterating
            trans.abort();
          } else {
            // advance to next entry
            cursor['continue']();
          }

        } else {
          // inform manager that all entries have been retrieved
          onDone(entries, lastKey, lastPrimaryKey, table, cnt);
        }

      };

      // return transaction
      return trans;
    }

    function handleAuthRequest(server, request) {
      var
        rid = request.rid,
        code = 0,
        req
      ;

      // exit if there is no response id or it does not begin with an "r"
      if (!isFullString(rid) || rid.charAt(0) != 'r') {
        server.log('auth fail', 'bad auth id: "' + rid + '"');
        // log how this request couldn't be handled
        return;
      }

      // validate auth request

      if (requests.has(rid)) {
        code = RSP_DUPLICATE_ID;
      } else if (!isFullString(request.channel)) {
        code = RSP_MISSING_CHANNEL;
      }

      // add request type
      request.type = 'auth';

      // exit if any error was found
      if (code) {
        server.respond(request, code);
        return;
      }

      // add to global auth requests
      // requests stay here until they are completed or cancelled
      requests.set(rid, request);

      // if there are auth event listeners
      if (server._hasSubs('auth')) {

        // manually authorize

        // create and publish auth handler
        server.fire(
          'auth',
          {
            allow: authAllow.bind(server, request),
            deny: authDeny.bind(server, request),
            channel: request.channel,
            credentials: request.creds
          }
        );

      } else {

        // auto authorize

        // add client to network now
        addClient(server, request);
      }

    }

    function hydrateBridgeFromStorageKey(bid, value) {
      var
        dead = value.charAt(0) == 0,
        detail = value.substr(1),
        bridge = {
          id: bid,
          dead: dead
        }
      ;
      // if bridge is dead
      if (dead) {
        // treat detail as timestamp
        bridge.died = detail;
      } else {
        // treat detail as url
        bridge.origin = detail;
      }

      return bridge;
    }

    function addBridge(server, bridge) {
      var bid = bridge.id;

      // add to bridges
      server.bridges.set(bid, bridge);

      // add channels
      bridge.channels = new Hash();
      // add clients
      bridge.clients = new Hash();

      // capture bridge id
      bridgeIds.push(bid);

      // re-calculate this server's delay
      updateServerDelay(server);

      return bridge;
    }

    // begin adding this client
    function addClient(server, request) {
      var
        rid = request.id,
        channelName = request.channel,
        networkChannel = resolveNetworkChannel(server, channelName),
        serverId = server.id,
        clientId = guish(),
        client = {
          id: clientId,
          bid: serverId,
          channel: channelName,
          stamp: now()
        }
      ;

      // remove request
      requests.del(rid);

      // if able to save client and/or tell network
      // errors are handled by #relayJoin
      if (server.relayJoin(client, request, networkChannel)) {
        // resolve server branch
        localChannel = server.channels.branch(channelName);
        // respond to request
        server.respond(request, RSP_ALLOW, {
          id: clientId,
          peers: mix(
            {},
            localChannel.items,
            networkChannel.items
          )
        });

        // add to server channel
        localChannel.set(clientId, client);
        // add to server clients
        server.clients.set(clientId, client);

        // handle case when client attempts a drop
        // using the request id
        // and remove when client uses it's true id
        server.on('host', function authVerifier(type, data, payload) {

          // if a client command occurs for this client...
          if (type == 'msg' && data.id == clientId) {
            removeVerifier();
          }

          // if a drop call references either this request or client
          if (type == 'drop' && (data == rid || data == clientId)) {
            // force the client id - in case it was the request
            payload.data = clientId;
            removeVerifier();
          }

          function removeVerifier() {
            // remove this subscriber
            server.off('host', authVerifier);
          }

        });
      }
    }

    function cancelAuthRequest(server, request, code) {
      var rid = request.id;

      // indicate request is being handled
      request.begun = 1;
      server.respond(request, code);
      removeAuthRequest(server, rid);
    }

    function removeAuthRequest(server, rid) {
      var
        request = requests.del(rid),
        networkChannel,
        clientId
      ;

      if (!request) {
        return;
      }

      networkChannel = request.nc;
      // if the associated network channel is not loaded
      if (!networkChannel.loaded) {
        // unsubscribe from loaded event
        networkChannel.off('loaded', request.chcb);
        // if no other clients need this channel...
        if (!--networkChannel.waiting) {
          // kill transaction
          networkChannel.trans.abort();
        }
      }

      // if there is a pending transaction
      if (request.trans) {
        // rollback adding client
        request.trans.abort();
      }

    }

    function authAllow(request) {
      var server = this;
      if (!request.begun) {
        addClient(server, request);
        return 1;
      }
      return 0;
    }

    function authDeny(request) {
      if (!request.begun) {
        cancelAuthRequest(this, request, RSP_DENIED);
        return 1;
      }
      return 0;
    }

    // function dropClient(server, clientId) {
    //   var
    //     // remove established client
    //     client = server.clients.del(clientId),
    //     channelName = client.channel,
    //     serverChannels = server.channels,
    //     channel = serverChannels.get(channelName),
    //     msgTable
    //   ;

    //   // if last client in channel
    //   if (channel.length == 1) {
    //     // remove channel
    //     serverChannels.del(channelName);
    //   } else {
    //     // remove client from channel
    //     channel.del(clientId);
    //   }
    //   // remove entry in IDB, then...
    //   IDBDropClient(clientId);
    //   // remove messages from this client
    //   IDBgetEntries(
    //     // table ref
    //     msgTable = DB.transaction('message', 'readwrite').objectStore('message'),
    //     // index
    //     'from',
    //     // only need the key
    //     1,
    //     // target entries from client
    //     clientId,
    //     function (clientData, key, primaryKey) {
    //       msgTable.delete(primaryKey);
    //     },
    //     isIE
    //     function () {
    //       server.unrelay(clientId);
    //     }
    //   );

    //   // "inform" network via LS
    //   server.relay(clientKey, {joins: [], drops: [clientId]});
    // }

    // send non-zero result if given targets are invalid
    function getRecipientCode(server, targets, senderId) {
      var
        serverClients = server.clients,
        networkClients = server.network.clients
      ;

      // exit when recipient is everybody
      if (targets === 0 || targets === '0') {
        return 0;
      }

      // decline any falsy value
      if (!targets) {
        return RSP_UNKNOWN_RECIPIENTS;
      }

      // ensure targets is an array - to consolidate validation logic
      if (!isArray(targets)) {
        targets = [targets];
      }

      // test all targets
      if (!targets.some(function (targetId) {
        return targetId == senderId ||
          serverClients.has(targetId) ||
          networkClients.has(targetId);
      })) {
        // fail when any one target is not a known peer
        return RSP_UNKNOWN_RECIPIENTS;
      }

    }

    // performs and returns IDB `delete`
    // returns delete request
    function IDBDropClient(clientId) {
      return DB
        .transaction('client', 'readwrite')
        .objectStore('client')
        ['delete'](clientId);
    }

    // add peer to new or existing bridge
    function addPeer(server, peer) {
      var
        pid = peer.id,
        network = server.network,
        bridge = server.bridges.get(peer.bid),
        channelName = peer.channel
      ;
      // add to bridge clients
      bridge.clients.set(pid, peer);
      // add to bridge channel
      // is this index needed?
      bridge.channels.branch(channelName).set(pid, peer);
      // add to network channel
      network.channels.get(channelName).set(pid, peer);
      // add to network peers
      network.clients.set(pid, peer);
    }

    // remove peer from network
    function removePeer(server, pid) {
      var
        network = server.network,
        // remove and retrieve from network peers
        peer = network.clients.del(pid),
        bridge,
        channelName
      ;

      if (peer) {
        channelName = peer.channel;
        bridge = server.bridges.get(peer.bid);

        // remove from bridge clients
        bridge.clients.del(pid);
        // remove from bridge channel
        bridge.channels.get(channelName).del(pid);
        // remove from network channel
        network.channels.get(channelName).del(pid);
        // indicate successful removal
        return 1;
      }
    }

    function ieGetPeerDropKey(bid, pid) {
      return protocolName + 'd' + bid + '-' + pid;
    }

    function ieGetPeerJoinKey(bid, pid) {
      return protocolName + 'j' + bid + '-' + pid;
    }


    function ieRemovePeerWarrant(pid) {
      if (hasKey(iePeerWarrants, pid)) {
        clearTimeout(iePeerWarrants[pid]);
        delete iePeerWarrants[pid];
      }
    }

    // retrieve or create a channel
    function resolveNetworkChannel(server, channelName) {
      var networkChannels = server.network.channels;

      // return existing channel
      if (networkChannels.has(channelName)) {
        return networkChannels.get(channelName);
      }

      // return new network channel
      return networkChannels.set(channelName, new NetChannel(server, channelName));
    }

    function w3cResolveRegistryChannel(server, channelName) {
      var registry = server.reg;

      if (hasKey(registry, channelName)) {
        return registry[channelName];
      }
      return registry[channelName] = {};
    }

    function w3cRegisterPeer(server, channelName, pid, bid, stamp) {

      w3cResolveRegistryChannel(server, channelName)[pid] = {
        bid: bid,
        stamp: stamp
      };

      return server.reg;
    }

    function w3cDeregisterPeer(server, channelName, pid) {
      var
        registry = server.reg,
        peerCnt = 0,
        registryChannel = registry[channelName],
        i
      ;
      if (registryChannel) {
        // loop through channel peers
        for (i in registryChannel) {
          // exit after more than one peer is found
          if (hasKey(registryChannel, i) && ++peerCnt > 1) {
            break;
          }
        }
        // if there is more than one peer in this channel...
        if (peerCnt > 1) {
          // remove peer from registered channel
          delete registryChannel[pid];
        } else {
          // remove entire channel
          // since removing the one peer would emptty the channel
          delete registry[channelName];
        }
      }
      return registry;
    }

    function pruneDeadBridge(bridge, bid) {
      // if this bridge no longer had a bury flag
      if (!getStorage(getBridgeKeyName(bid))) {
        // clear burial timer
        clearTimeout(bridge.timer);
        // remove this dead bridge
        deadBridges.del(bid);
      }
    }

    function updateServerDelay(server) {
      // sort bridges
      bridgeIds.sort();
      // set time this server should wait before burying other bridges
      server._delay = getBridgeKillDelayFromId(server.id);
    }

    // remove from server
    function killBridge(server, bid, when) {
      var
        bridge = server.bridges.del(bid),
        deadPeers
      ;

      // exit if the bridge does not exist...
      if (!bridge) {
        return;
      }

      // add to global dead bridge queue
      deadBridges.set(bid, bridge);

      // remove from bridges index
      bridgeIds.splice(bridgeIds.indexOf(bid), 1);

      // notify server that this bridge is gone
      server.fire('killed bridge', bridge);

      // exit if destroyed
      if (server.state != STATE_READY) {
        // let some other bridge do the dirty work
        return;
      }

      // collect peer ids from this bridge
      // method removes peers from network channels and clients
      deadPeers = bridge.clients.each(discardBridgePeers, server);

      // notify host of dead clients
      if (deadPeers.length) {
        server.tell('net', {joins:[], drops: deadPeers});
      }

      // schedule burying this bridge
      bridge.timer = setTimeout(
        buryBridge.bind(server, bid),
        server._delay
      );

    }

    // remove from IDB
    function buryBridge(bid, callback) {
      var
        server = this,
        bridge = deadBridges.del(bid)
      ;

      // only bury the dead
      if (bridge) {
        removeBridgeEntries(bid, callback);
      }
    }

    function cancelBridgeTimer(bridge) {
      // clear the bridge timeout
      clearTimeout(bridge.timer);
    }

    function removeBridgeEntries(bid, callback) {
      // delete messages from this bid
      tableDeleteEntriesOnIndex(
        // table
        'message',
        // index
        'bid',
        // range
        bid,
        // callback
        function () {
          // remove localstorage key
          // the resulting event tells other bridges
          // to avoid doing the same
          LS.del(getBridgeKeyName(bid));

          // tell callback this bridge is buried
          if (callback) {
            callback(bid);
          }
        }
      );
    }

    function discardBridgePeers(peer, pid) {
      var
        server = this,
        network = server.network
      ;
      // remove from network clients
      network.clients.del(pid);
      // remove from network channel
      network.channels.get(peer.channel).del(pid);

      return pid;
    }

    // delegate unload event
    function delegateUnloadEvent() {
      systemBus.fire('unload');
    }


    // handle storage key addition or update
    function handleStorageEvent(key, value) {
      var
        storageCmds = (value === null || value == undefined) ? storageRemovalCmds : storageUpdateCmds,
        ln = storageCmds.length,
        cmd,
        challenge,
        proceed
      ;

      // loop over local storage key matches
      while (--ln) {
        // alias command
        cmd = storageCmds[ln];
        // capture key challenge
        challenge = cmd[2];

        // if the challenge is just a string
        if (cmd[1]) {
          // proceed when the key matches the string
          proceed = challenge == key;
        } else if (cmd[3]) {
          // the key must match parts of the regxp
          proceed = key.match(challenge);
        } else {
          // the key must satisfy the regxp
          proceed = challenge.test(key);
        }
        // execute handler if key met the challenge
        if (proceed) {
          // passing proceed - which could be an array of matching sub-strings
          cmd[0](this, value, proceed, key);
          break;
        }
      }
    }

    /*
      if (hasKey(localStorageCommands, key)) {

        // when a known key updates...
        //  - message key prompts IDB read
        //  - channel key (w3c) updates partial network

        // if storage value is valid...
        if (hasKey(value, 'bid') && hasKey(value, 'data')) {
          // handle with pre-built command
          localStorageCommands[key].call(server, value.bid, value.data);
        }

      } else if (parts = key.match(r_bridgeKey)) {

        // when a bridge key updates...
        // - bridge has been added
        // - bridge has expired

        // we must determine if it's a new or expired bridge

        // alias bridge id
        bid = parts[1];
        // parse bridge details from value
        bridge = hydrateBridgeFromStorageKey(bid, value);

        // if this is a death warrant...
        if (bridge.dead) {
          // kill local bridge network now
          // schedules burial later, based on when it died
          killBridge(server, bid, bridge.died);
        } else {
          // add bridge if it does not already exist
          addBridge(server, bridge);
        }

      } else if (
        parts = key.match(r_iePeerJoin) &&
        value &&
        (bid = parts[1]) != server.id &&
        server.bridges.has(bid) &&
        typeof value == 'object'
      ) {

        // a client was added to the network
        //

        // add id to client object
        value.id = parts[2];
        // process joined client
        handleJoinedClient(server, bid, value);


      } else if (parts = key.match(r_ieChannelKey)) {

        // when a channel key updates (on IE)...
        // - reconcile the given channel via IDB

        // get channel
        channelName = parts[1];

        // if this is an existing server channel
        if (server.channels.has(channelName)) {
          // update network channel
          resolveNetworkChannel(server, channelName).load();
        }

      }

    */

    // relay array of messages for this server's clients
    function readMessages(entries, cnt, lastKey) {
      var
        server = this,
        clients = server.clients,
        networkPeers = server.network.clients,
        channels = server.channels,
        msgs = [],
        peer,
        key,
        msg
      ;

      // capture lastKey, for next read
      server._lastKey = lastKey;

      // only relay message that target this server's clients
      for (key in entries) {
        if (hasKey(entries, key)) {
          msg = entries[key];
          peer = networkPeers.get(msg.from);
          // if peer is known and we have clients in this channel...
          if (peer && channels.has(peer.channel)) {
            // if broadcast or server has a recipient
            if (
              !msg.to ||
              msg.to.some(targetServerClients)
            ) {
              msgs.push(msg);
            }
          }
          // log error if sent from unknown peer?
          // could occur if clearing old peers is slow
          // not a real problem, except the message is not received
        }
      }

      // if there are messages to send...
      if (msgs.length) {
        server.relay(msgs);
      }

      function targetServerClients(clientId) {
        return clients.has(clientId);
      }
    }

    function handleNewPeer(server, bid, peer) {

    }

    // route messages from server port
    /*
    event.data structure:
    {
      mid: <int>,
      type: <string>,
      data: <mixed>
    }
    */
    function handlePostMessageEvent(evt) {
      var
        server = this,
        evtType = evt.type
      ;

      // exit on unknown type
      if (
        !evtType ||
        !hasKey(postMessageCommands, evtType)
      ) {
        // log error
        // destroy server?
        return;
      }
      // log post message for manipulation??
      server.fire('host', evtType, evt.data, evt);

      // route to type handler
      postMessageCommands[evtType].call(server, evt.data, evt);

    }

    function tableDeleteEntriesOnIndex(tableName, indexName, rangeKey, allDone) {
      var
        promised = 0,
        done = 0,
        table = DB.transaction([tableName], 'readwrite').objectStore(tableName)
      ;
      // ensure allDone is a function
      if (!allDone) {
        allDone = noOp;
      }
      IDBgetEntries(
        // table
        table,
        // index
        indexName,
        // key only flag
        1,
        // key range
        rangeKey,
        // on found
        function (key, primaryKey) {
          // track promise to delete this entry
          ++promised;
          // ask to delete entry and await log completion
          table['delete'](primaryKey).onsuccess = oneDown;
        },
        // on done
        function () {
          // if no deletions were promised...
          if (!promised) {
            // call all done - since there's nothing to delete!
            allDone();
          }
        }
      );

      function oneDown() {
        if (promised == ++done) {
          allDone();
        }
      }
    }

    // allows handling next client event
    function unlockAndRunQueue() {
      // unlock queue
      relayQueueLocked = 0;
      // resume queue next
      next(runRelayQueue());
    }

    // process next client event
    function runRelayQueue(server) {
      var
        relayQueue = server.rq,
        relayDeets,
        request
      ;

      // exit if queue is closed or there are no messages to relay
      if (relayQueue.l || !relayQueue.length) {
        return;
      }

      // lock queue
      relayQueue.l = 1;
      // retrieve relay request
      relayDeets = relayQueue.shift();
      // if there are subscribers of this event
      if (server._hasSubs('relay')) {
        // take command off queue and create client message request
        request = new RelayRequest(relayQueue.shift());
        wrapRequestMethods(request);
        // add as pending relay
        bridge.pendingRelay = request;
        // announce client event request
        bridge.fire('relay', request);
      } else {
        request.allow();
      }
    }

    function makePayloadForChannelRelay(server, type, client) {
      return {
        bid: server.id,
        type: type,
        data: {
          channel: client.channel,
          id: client.id
        }
      };
    }

    // CLASSES

    // basic event emitter
    function EventEmitter() {}
    mix(EventEmitter.prototype, emitterPrototype);

    // returns true when there is a subscriber for the given event
    EventEmitter.prototype._hasSubs = function (eventName) {
      var me = this;

      return hasKey(me, '_evts') &&
        hasKey(me._evts, eventName) &&
        me._evts[eventName].length;
    };


    // basic key/value store
    function Hash(val) {
      var
        hash = this,
        items = {},
        key,
        length = 0
      ;

      // if given an initial value
      if (typeof val == 'object') {
        for (key in val) {
          if (hasKey(val, key)) {
            // copy key and value
            items[key] = val[key];
            // increment length
            ++length;
          }
        }
      }

      // set as items
      hash.items = items;
      hash.length = length;
    }

    mix(Hash.prototype, {
      // add hash to items, if not present
      branch: function (key) {
        var
          hash = this,
          child
        ;
        if (hash.has(key)) {
          return hash.get(key);
        }
        child = new Hash();
        child._key = key;
        return hash.set(key, child);
      },
      set: function (key, value) {
        var hash = this;

        if (!hash.has(key)) {
          ++hash.length;
        }
        hash.items[key] = value;

        return value;
      },
      del: function (key) {
        var
          hash = this,
          removedValue = hash.get(key)
        ;

        if (removedValue) {
          delete hash.items[key];
          --hash.length;
          return removedValue;
        }
      },
      has: function (key) {
        return hasKey(this.items, key);
      },
      get: function (key, defaultValue) {
        var hash = this;

        if (hash.has(key)) {
          return hash.items[key];
        } else if (defaultValue) {
          // set first value with key
          return hash.set(key, defaultValue);
        }
      },
      clear: function () {
        var hash = this;

        hash.items = {};
        hash.length = 0;
      },
      each: function (fn, context) {
        var
          hash = this,
          items = hash.items,
          val,
          returnedValues = [],
          key
        ;
        for (key in items) {
          if (hasKey(items, key)) {
            val = fn.call(context, items[key], key);
            if (val !== hashIgnoreFlag) {
              returnedValues.push(val);
            }
          }
        }
        return returnedValues;
      },
      keys: function () {
        return objectKeys(this.items);
      }
    });

    function Queue(context) {
      var q = this;

      q._ary = [];
      q._o = context;

      q._cb = function () {
        q.active = 0;
        q.run();
      };
    }

    mix(Queue.prototype, {

      // busy flag for queues
      active: 0,

      add: function (fn) {
        var q = this;

        q.ary.push(fn);
        q.run();
      },

      clear: function () {
        this.ary.length = 0;
      },

      // process first in first out
      run: function () {
        var q = this;

        if (!q.active && q.ary.length) {
          q.active = 1;
          q.ary.unshift().call(q._o, q._cb);
        }
      }

    });

    function NetChannel(server, channelName) {
      var me = this;

      // init super
      Hash.call(me);

      me.server = server;
      me.name = channelName;

      // load network peers
      me.load();
    }
    // extend hash
    NetChannel.prototype = new Hash();
    mix(NetChannel.prototype, emitterPrototype);
    // load network
    // use browser-based approach
    NetChannel.prototype.load = isIE ?

      // ie - cycle through peer keys
      function () {
        var
          me = this,
          server = me.server,
          serverId = server.id,
          bridges = server.bridges,
          channelName = me.name
        ;
        // process peer keys
        LS.each(function (peer, key) {
          var
            matches,
            bid,
            pid
          ;
          // if not a peer object
          // checking "peer" since IE leaves ghost keys
          if (peer && (matches = key.match(r_iePeerJoin))) {
            /*
              // peer structure
              {
                channel: <string>,
                stamp: <int>
              }
            */

            // alias matches
            bid = matches[1];
            pid = matches[2];

            // exit when peer...
            if (
              // from this server
              bid == serverId ||
              // different channel
              peer.channel != channelName ||
              // from unknown bridge
              !bridges.has(bid) ||
              // has a corresponding peer drop key
              LS.has(ieGetPeerDropKey(bid, pid))
            ) {
              return;
            }

            // flesh out peer members
            peer.id = pid;
            peer.bid = bid;
            // capture to channel hash
            me.set(pid, peer);
          }

        });
      } :
      // w3c hydrate peers from server registry
      function () {
        var
          me = this,
          server = me.server,
          bridges = server.bridges,
          registry = server.reg,
          channelName = me.name,
          registryChannel,
          registryPeer,
          pid,
          bid
        ;
        // exit if this channel is not registred...
        if (!hasKey(registry, channelName)) {
          return;
        }
        // alias channel registry
        registryChannel = registry[channelName];
        // scan "peers" in channel
        /*
          // peer structure
          {
            bid: <bridge>
            stamp: <int>
          }
        */
        for (pid in registryChannel) {
          if (hasKey(registryChannel, pid)) {
            // alias raw entry
            registryPeer = registryChannel[pid];
            bid = registryPeer.bid;
            // if peer is from known bridge...
            if (bridges.has(bid)) {
              // clone & capture peer to channel hash
              // registry objects can't be augmented
              me.set(pid, {
                id: pid,
                bid: bid,
                stamp: registryPeer.stamp,
                channel: channelName
              });
            } else {
              // (cleanly) remove expired peer
              delete w3cDeregisterPeer(server, channelName, pid);
            }
          }
        }
      }
    ;

    function Server() {
      var server = this;

      // all bridge channels and clients
      server.network = {
        channels: new Hash(),
        clients: new Hash()
      };

      // all bridges - bridges have clients and channel hashes too
      server.bridges = new Hash();

      // local channels
      server.channels = new Hash();
      // local clients
      server.clients = new Hash();
      server.initKeys();
    }

    Server.prototype = new EventEmitter();
    Server.prototype.constructor = Server;

    mix(Server.prototype, {

      state: STATE_INITIAL,

      // wait first window "message" event
      startup: function () {
        var server = this;

        if (server.state != STATE_INITIAL) {
          // log error?
          return;
        }

        // set to queued state
        server.state = STATE_QUEUED;

        // bind and use init - which expects a message event
        server.onpost = server.init.bind(server);

        // listen for window-level message
        bind(scope, 'message', server.onpost);
        // watch for unload
        server.rigUnload();
      },

      // process this postMessage event
      init: function (evt) {
        var
          server = this,
          payload,
          hostOrigin,
          hostNetwork
        ;

        // exit when beyond queued
        if (server.state > STATE_QUEUED) {
          server.log('already initialized');
          return;
        }

        // unbind window-level "message" event handler
        server.unrigHostMsg();

        // set state to pending...
        // until the database connection is opened
        server.state = STATE_PENDING;

        // validate event parameter
        if (
          // evt is not an object
          typeof evt != 'object' ||
          // missing ports
          !evt.ports ||
          // missing port
          !(server.port = evt.ports[0]) ||
          // event data is not an object
          typeof (payload = evt.data) != 'object' ||
          // event data is falsy
          !payload ||
          // missing "origin" member
          !isFullString(hostOrigin = evt.origin) ||
          // protocol mismatch
          payload.protocol != protocolName ||
          // invalid network name
          !isFullString(hostNetwork = payload.network)
        ) {
          // exit, since we can't work with a bad event
          server.log('bad init event', evt);
          // prevent attempts to init twice
          server.destroy();
          return;
        }

        // capture host origin
        server.origin = hostOrigin;
        // capture network
        server.name = hostNetwork;

        // if DB connection has been established...
        if (sysReady) {
          // complete initialization now
          completeServerInitialization.call(server);
        } else {
          // (otherwise) resume once system is ready
          systemBus.on('sysRet', completeServerInitialization.bind(server));
        }

      },

      readMsgs: function () {
        var server = this;

        server.getEntries('message', readMessages, server._lastKey);
      },

      // getEntries: function (tableName, indexName, rangeKey, onFound, onDone) {
      //   var
      //     server = this,
      //     dbq = server.dbq,
      //     dbLocks = server.locks
      //   ;

      //   // if a read of this table is already queued...
      //   if (dbLocks[tableName]) {
      //     // run queue now
      //     dbq.run();
      //   } else {

      //     // (otherwise) when this table is not queued to be read

      //     // add lock for this table name - the value doesn't matter
      //     dbLocks[tableName] = 1;

      //     // queue call to read table
      //     dbq.add(function (queueDone) {
      //       // release lock
      //       dbLocks[tableName] = 0;
      //       // get entries
      //       IDBgetEntries(
      //         tableName,
      //         callback,
      //         startingBound,
      //         queueDone
      //       );
      //     });
      //   }
      // },

      // writes key and destroy self if it fails
      setKey: function (key, value) {
        try {
          LS.set(key, value);
          return 1;
        } catch (e) {
          // log error?
          this.destroy();
        }
      },

      // send message to host
      tell: function (type, data, sent) {
        this.port.postMessage({
          mid: ++messageTick,
          type: type,
          sent: sent || now(),
          data: data
        });
      },

      // send response code to host
      respond: function (req, code, body) {
        var
          rid = req.rid,
          rsp = {
            id: rid,
            status: code
          }
        ;
        // add body if there is one
        if (body) {
          rsp.body = body;
        }
        // remove request
        requests.del(rid);
        // tell host
        this.tell(req.type + '-rsp', rsp);
      },

      // update network via localStorage
      relay: isIE ?
        // sets given key to current date
        // the change will be discovered by other bridges
        // who will reconcile with IDB
        function (key) {
          this.setKey(key, now());
        } :

        // sets the given key to the given data
        // data wrapped for bridge identification
        // other bridges will see the full message
        function (key, data) {
          var server = this;

          server.setKey(key, {
            bid: server.id,
            data: data
          });

        },

      // unbind window-level message listener
      unrigHostMsg: function () {
        var server = this;

        // only when in queued state...
        if (server.onpost) {
          // remove "message" event listener
          unbind(scope, 'message', server.onpost);
          // dereference "message" event handler
          server.onpost = 0;
        }
      },

      // listen for unload
      rigUnload: function () {
        var server = this;

        if (!server.onunload) {
          // destroys self with unload flag
          server.onunload = server.destroy.bind(server, 1);
          bind(scope, 'unload', server.onunload);
        }
      },

      // stop listening for unload
      unrigUnload: function () {
        var server = this;

        if (server.onunload) {
          unbind(scope, 'unload', server.onunload);
          server.onunload = 0;
        }
      },

      // listen for storage events
      rigLS: function () {
        var
          server = this,
          cb
        ;
        // start monitor for first server
        if (!serverInsts.length) {
          LS.watch();
        }
        // bind to storage events
        cb =
        server.onstorage =
          handleStorageEvent.bind(server);
        // watch "network" for storage events
        systemBus.on('ls-update', cb);
        systemBus.on('ls-delete', cb);
      },

      // stop listening to storage events
      unrigLS: function () {
        var
          server = this,
          cb = server.onstorage
        ;

        if (cb) {
          // stop watching storage
          systemBus.off('ls-update', cb);
          systemBus.off('ls-delete', cb);
          // dereference handler
          server.onstorage = 0;
          // stop monitor after last server
          if (!serverInsts.length) {
            LS.unwatch();
          }
        }
      },

      // capture network registry
      regNet: isIE ?
        // ie doesn't use this approach
        // since it relies on storage events
        noOp :

        // capture registry
        // this is kept in sync via change events
        function () {
          var
            server = this,
            registry = LS.get(w3cRegKey) || {}
          ;
          server.reg = registry;
        },

      // set up keys
      initKeys: isIE ?
        function () {
          // array of keys to eventually discard
          this.ckeys = [];
        } :
        noOp,

      // destroy keys
      cleanKeys: isIE ?
        function () {
          var
            keys = this.ckeys,
            ln = keys.length
          ;
          // remove all client keys
          while (ln--) {
            LS.del(keys[ln]);
          }
        } :
        function () {
          var server = this;

          // when other bridges remain...
          if (bridgeIds.length) {
            // remove remaining clients from map
            server.clients.each(function (client, clientId) {
              w3cDeregisterPeer(server, client.channel, clientId);
            });
            // save map
            // using server method, despite ocurring on destroy
            // in order to avoid exception
            server.setKey(w3cRegKey, server.reg);
          } else {

            // (otherwise) when this is the last bridge

            // remove all shared keys
            LS.del(w3cRegKey);
            LS.del(w3cClientKey);
          }
        },

      // destroy
      destroy: function (unloading) {
        var
          server = this,
          lastState = server.state,
          serverId = server.id,
          serverKey = server.key
        ;

        // exit if already destroyed
        if (lastState == STATE_DESTROYED) {
          return;
        }

        // update state
        server.state = STATE_DESTROYED;

        if (serverId) {
          // remove from bridgeIds
          bridgeIds.splice(bridgeIds.indexOf(serverId), 1);
          // remove from managed instances
          serverInsts.del(serverId);
        }

        // if "registered" in localStorage
        if (serverKey) {
          // put out death warrant
          server.setKey(serverKey, '0' + now());
          // clean IDB if not unloading
          if (!unloading) {
            removeBridgeEntries(serverId);
          }
        }

        // unbind window-level "message" event handler
        server.unrigHostMsg();

        // stop listening to localstorage events
        server.unrigLS();
        // stop listening to unload
        server.unrigUnload();

        // detach all events
        server.off();

        // remove various keys
        server.cleanKeys();
        // remove lingering bridge timers
        server.bridges.each(cancelBridgeTimer);

        // if there are no more bridges...
        if (!bridgeIds.length) {
          // clean (shared) msg key
          LS.del(msgKey);
        }
      },

      log: function (type, msg) {
        this.fire('error', type, msg);
      },

      relayJoin: isIE ?
        // add key per joined client
        function (client, request) {
          // build key specific to this client
          var
            server = this,
            clientKey = ieGetPeerJoinKey(server.id, client.id)
          ;
          // capture client key
          server.ckeys.push(clientKey);
          // return result to indicate success/failure of attempt
          // join key remains until:
          // 1. client is removed by (a) bridge
          // 2. bridge dies
          return server.setKey(clientKey, {
            channel: client.channel,
            stamp: client.stamp
          });
        } :
        function (client, request) {
          var
            server = this,
            payload,
            channelName = client.channel,
            clientStamp = client.stamp
          ;

          // if registry was successfully updated...
          if (
            server.setKey(w3cRegKey, w3cRegisterPeer(
              server,
              channelName,
              client.id,
              server.id,
              clientStamp
            ))
          ) {
            // if there are other peers to inform
            if (server.network.channels.branch(channelName).length) {
              payload = makePayloadForChannelRelay(server, 'join', client),
              payload.data.stamp = clientStamp;
              // notify network - use result to declare success
              return server.setKey(w3cClientKey, payload);
            }
            return 1;
          }
        },

      relayDrop: isIE ?
        function (client) {
          // build key specific to this client
          var
            server = this,
            clientKey = ieGetPeerDropKey(server.id, client.id)
          ;
          // capture added key
          server.ckeys.push(clientKey);
          // drop key remains until:
          // 1. client is removed by (some) bridge
          // 2. bridge dies
          return server.setKey(clientKey, 1);
        } :
        function (client) {
          var
            server = this,
            channelName = client.channel
          ;

          // if sucessfully updated the network registry
          if (
            server.setKey(w3cRegKey, w3cDeregisterPeer(
              server,
              channelName,
              client.id
            ))
          ) {
            // if there are other peers to inform...
            if (server.network.channels.branch(channelName).length) {
              // update client key
              // notifies other bridges that we dropped a client
              // use result to declare success
              return server.setKey(
                w3cClientKey,
                makePayloadForChannelRelay(server, 'drop', client)
              );
            }

            return 1;
          }
        }

    });

    // manage request to relay client events
    function RelayRequest(msg) {
      var me = this;
      me.msg = msg;
    }

    mix(RelayRequest.prototype, {

      allow: function () {
        var
          me = this,
          msg = me.msg,
          relayed = 0,
          sender = bridgeClients[msg.from],
          recipients = msg.to,
          isBroadcast = !recipients,
          channelName = sender.channel,
          bridgePeerCount = bridgeChannelCnts[channelName],
          networkPeerCount = networkChannelCnts[channelName]
        ;

        // remove this relay request
        bridge.pendingRelay = null;

        // only relay if there are other clients in this channel
        if (networkPeerCount > 1) {
          // relay back to host when...
          if (
            // there are other channel clients on this bridge
            bridgePeerCount > 1 &&
            // and...
            (
              // this is a broadcast
              isBroadcast ||
              // or a recipient is on this bridge
              hasAtLeastOneKey(bridgeClients, recipients)
            )
          ) {
            relayToHost(msg);
            relayed = 1;
          }

          // only relay to network when...
          if (
            // there are more clients outside this bridge
            bridgePeerCount < networkPeerCount &&
            // and...
            (
              // this is a broadcast
              isBroadcast ||
              // or, some recipients are not local
              hasNotAtLeastOneKey(bridgeClients, recipients)
            )
          ) {
            // relay message to network
            broadcast('client', msg);
            relayed = 1;
          }

          // if anything got relayed
          if (relayed) {
            fireMessageEvent(msg);
          }

        }
        unlockAndRunQueue();
      },

      deny: unlockAndRunQueue,

      ignore: unlockAndRunQueue

    });

    // create server instance
    Subetha.bridge = new Server();

    // if document has not loaded...
    if (!doc.body) {
      // await first ping
      Subetha.bridge.startup();
    }

    return Subetha;
  }

  // initialize and expose subetha, based on the environment
  if (inAMD) {
    define(initSubEthaBridge);
  } else if (inCJS) {
    module.exports = initSubEthaBridge();
  } else if (!scope.Subetha) {
    scope.Subetha = initSubEthaBridge();
  }
}(
  typeof define == 'function', // amd test
  typeof exports != 'undefined', // node test
  localStorage, Array, Date, Math, navigator.userAgent, this
);
