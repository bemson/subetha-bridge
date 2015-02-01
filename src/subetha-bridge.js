/*jshint -W056 */
/* global define, require, module */
/*!
 * SubEtha-Bridge
 * http://github.com/bemson/subetha-bridge/
 *
 * Copyright 2014 Bemi Faison
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

!function (inAMD, inCJS, localStorage, Array, Date, Math, scope, undefined) {

  // dependent module initializer
  function initSubEthaBridge() {

    var
      // externals
      cipher = new ((inCJS || inAMD) ? require('morus') : scope.Morus)(),

      // builtins & shorthand
      JSONstringify = JSON.stringify,
      JSONparse = JSON.parse,
      LS = localStorage,
      mathRandom = Math.random,
      isArray = (typeof Array.isArray === 'function') ?
        Array.isArray :
        function (obj) {
          return obj instanceof Array;
        },
      stringfromCharCode = String.fromCharCode,
      doc = document,

      // prototype aliases
      protoSlice = Array.prototype.slice,
      protoHas = Object.prototype.hasOwnProperty,
      protoClientDrop,

      // guid
      guidPattern = 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx',
      rxp_guid = /[xy]/g,

      // version & identification
      protocolVersion = 'se-0',
      bridgeId = guid(),
      bridgeNetworkName,

      // initialization
      initialized = 0,
      destroyed = 0,
      initedPeers = 0,


      // security
      backtick = '`',
      lastStamp,
      host = scope.parent,
      speakerKey,
      r_validClientMsg,
      r_validStorageEvent = new RegExp(
        protocolVersion + backtick +
        '[0-9a-f-]{36}' + backtick +
        '\\d+' + '\\{.+\\}$'
      ),
      origin = location.origin || location.protocol + '//' + (location.port ? location.port + ':' : '') + location.hostname,
      storagePfx = protocolVersion + backtick + bridgeId + backtick,
      unsupported =
        // not in an iframe
        host === scope ||
        // has no postmessage
        typeof host.postMessage != 'function' ||
        // has no localstorage
        typeof LS != 'object' ||
        typeof LS.getItem != 'function' ||
        typeof LS.setItem != 'function',

      // ie local storage workaround
      isIE910 = /msie\s[91]/i.test(navigator.userAgent),
      isIE11 = !isIE910 && /trident/i.test(navigator.userAgent),
      isIE = isIE910 || isIE11,
      ie11ManifestTimer,
      ieNetworkBuffer = [],
      ieCallQueue = [],
      ieManifest,
      ieCookieNameStr = protocolVersion + '=',
      ieCookieNameStrLength = ieCookieNameStr.length,
      ieCookiePathStr = ';path=/',
      ieCookieRemoveStr = ieCookieNameStr + ';expires=0' + ieCookiePathStr,
      ieTickValue = 0,
      ieBridgeIds = {},
      ieBridgeTicks,
      ieMsgTimer,
      ieLastMsgTime = 0,
      ieMsgDelay = 100,
      ie_r_validInitialStorageEvent = new RegExp(
        protocolVersion + backtick +
        '[0-9a-f-]{36}' + backtick +
        '\\d+' + '\\[.+\\]$'
      ),

      // localstorage keys
      netKeySuffix = '-net',
      msgKeySuffix = '-msg',
      netKey = (isIE ? bridgeId : protocolVersion) + netKeySuffix,
      msgKey = (isIE ? bridgeId : protocolVersion) + msgKeySuffix,

      // network tracking
      networkClients = {},
      networkClientsCnt = 0,
      networkChannels = {},
      networkChannelCnts = {},
      pendingAuthReqs = {},

      // bridge (local) tracking
      bridgeClients = {},
      bridgeClientsCnt = 0,
      bridgeChannels = {},
      bridgeChannelCnts = {},

      // "net" payload vars
      dropQueue = {},
      joinQueue = {},
      networkChangeTimer,

      // "client" payload
      relayQueue = [],
      relayQueueLocked = 0,

      // events
      AUTH_EVENT = 'auth',
      RELAY_EVENT = 'relay',
      MSG_EVENT = 'message',
      ERROR_EVENT = 'error',
      DROP_EVENT = 'drop',
      JOIN_EVENT = 'join',
      INITIALIZE_EVENT = 'initialize',

      // RESPONSE CODES
      CLIENT_RSP_HANDLED = 1,
      CLIENT_RSP_QUEUED = 1,
      CLIENT_RSP_MALFORMED = 1,
      CLIENT_RSP_DUPLICATE = 1,
      CLIENT_RSP_MISSING_CHANNEL = 1,
      CLIENT_RSP_MISSING_COMMAND = 1,

      // post message utility flag
      canPostObjects = isIE ? 0 : !!function () {
        var yes = 1;

        // synchronous check for postMessage object support!
        // thx gregers@http://stackoverflow.com/a/20743286
        try {
          scope.postMessage({
            toString: function () {
              yes = 0;
            }
          }, '*');
        } catch (e) {}

        return yes;
      }(),

      // postmessage
      postMessage = canPostObjects ?
        function (msg) {
          host.postMessage(msg, '*');
        } :
        function (msg) {
          host.postMessage(JSONstringify(msg), '*');
        },

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
      bind = scope.attachEvent ?
        function (object, eventName, callback) {
          object.attachEvent('on' + eventName, callback);
        } :
        function (object, eventName, callback) {
          object.addEventListener(eventName, callback, false);
        },
      unbind = scope.attachEvent ?
        function (object, eventName, callback) {
          object.detachEvent('on' + eventName, callback);
        } :
        function (object, eventName, callback) {
          object.removeEventListener(eventName, callback, false);
        },

      queueNetworkRelay = isIE ?
        function (type, msg) {
          // buffer message
          ieNetworkBuffer.push(wrapStorageMessage(type, msg));
          // prepare to send message if not already waiting
          if (!ieMsgTimer) {
            queueCall(ieSendNetworkBuffer);
          }
        } :
        function (type, msg) {
          sendStorageMessage(wrapStorageMessage(type, msg));
        },

      queueCall = isIE ?
        // hold call to function until throttle triggers
        function (fnc, args) {
          ieCallQueue.push([fnc, args]);
          // log('queued call ' + ieCallQueue.length + ' for invocation');
          ieRunQueue();
        } :
        // call function immediately and avoid queue
        runCall,

      postMessageCommands = {

        // pass through client event to relevant recipients
        /*
        event data structure
        {                             [payload]
          key: <speaker=key>,
          mid: <guid>,
          type: 'client',
          msg: {                      [msg]
            type: <client-type>,
            from: <guid>,
            to: [...],
            data: ...                 // optional
          }
        }
        */
        client: function (payload, evt) {
          var
            msg = payload.msg,
            initialLength;

          // only queue if client event has proper structure
          if (
            // msg is an object
            typeof msg == 'object' &&
            // type is a string
            isFullString(msg.type) &&
            // comes from a registered client
            protoHas.call(bridgeClients, msg.from)
          ) {
            // get initial queue length - before adding our event
            initialLength = relayQueue.length;
            // queue client message
            relayQueue.push({
              msg: msg,
              sent: evt.timeStamp
            });
            // run queue
            runRelayQueue();
            // if the newly queued event was handled...
            if (relayQueue.length <= initialLength) {
              // return code for "processed"
              return CLIENT_RSP_HANDLED;
            }
            // return code for "in-queue"
            return CLIENT_RSP_QUEUED;
          }
          // return code for "malformed"
          // reasons span from any failed conditional expression
          return CLIENT_RSP_MALFORMED;
        },

        // handle client authentication request
        /*
        event data structure
        {                                 [payload]
          key: <speaker-key>,
          mid: <guid>,
          type: 'auth',
          msg: {                          [msg]
            id: <client-id>,
            channel: <channel-name>,
            creds: [ <credential>, ... ]
          }
        }
        */
        auth: function (payload, evt) {
          // create request object
          var
            clientData = payload.msg,
            clientId = clientData.id,
            creds = clientData.creds,
            request;

          log('handling auth request!');

          // exit/ignore when already joined or authing
          if (
            protoHas.call(pendingAuthReqs, clientId) ||
            protoHas.call(networkClients, clientId)
          ) {
            return CLIENT_RSP_DUPLICATE;
          }

          // exit if there is no channel specified
          if (!isFullString(clientData.channel)) {
            return CLIENT_RSP_MISSING_CHANNEL;
          }

          // add url to client data
          clientData.origin = evt.origin;
          // create request
          request = new AuthRequest(clientData, payload.mid);

          // if there are no listeners for this event
          if (
            !protoHas.call(bridge, '_evts') ||
            !protoHas.call(bridge._evts, AUTH_EVENT) ||
            !bridge._evts[AUTH_EVENT].length
          ) {
            // auto authenticate user (synchronously)
            request.allow();
          } else {
            // manually authenticate (asynchronously)

            // add to pending clients
            pendingAuthReqs[clientId] = request;

            // make request unique
            wrapRequestMethods(request);

            // publish authentication request
            if (creds.length) {
              bridge.fire.apply(bridge, [AUTH_EVENT, request].concat(creds));
            } else {
              bridge.fire(AUTH_EVENT, request);
            }
          }
        },

        // handle the host dropping client
        /*
        event data structure
        {                                 [payload]
          key: <speaker-key>,
          mid: <guid>,
          type: 'drop',
          msg: <guid>                          [msg]
        }
        */
        drop: function (payload) {
          var
            clientId = payload.msg,
            client;

          if (protoHas.call(bridgeClients, clientId)) {
            // drop registered client
            client = bridgeClients[clientId];
            // immediately remove client from bridge and network
            unregisterBridgeClient(client);
            unregisterNetworkClient(client);
            // if client was never announced, prepare to broadcast network change
            if (!protoHas.call(joinQueue, clientId)) {
              queueNetworkChange(client, dropQueue);
            }
          } else if (protoHas.call(pendingAuthReqs, clientId)) {
            // ignore auth request
            pendingAuthReqs[clientId].ignore();
          }
        }

      },

      localStorageCommands = {

        // process adding/removing clients from network channels
        /*
        {                   [payload]
          type: 'net',
          bid: <guid>,
          msg: {            [msg]
            joins: [
              {
                id: <guid>,
                origin: <uri>,
                channel: <channel-name>,
                start: <date>,
                bid: <guid>
              },
              ...
            ],
            drops: [
              {
                id: <guid>,
                channel: <channel-name>
              },
              ...
            ]
          }
        }
        */
        net: function (msg) {
          var
            joins = msg.joins,
            drops = msg.drops,
            clientId,
            client,
            clientData,
            ln,
            shareWithHost,
            hostPayload = {joins:[], drops: []};

          // process newly added clients
          ln = joins.length;
          while (ln--) {
            clientData = joins[ln];
            client = new NetworkClient(clientData);
            registerNetworkClient(client);
            fireJoinEvent(client);
            // pass-thru when there are bridge clients in this channel
            if (bridgeChannelCnts[client.channel]) {
              // remove bid member form clientData
              delete clientData.bid;
              hostPayload.joins.push(clientData);
              shareWithHost = 1;
            }
          }

          // process removed clients
          ln = drops.length;
          while (ln--) {

            clientData = drops[ln];
            clientId = clientData.id;

            if (protoHas.call(networkClients, clientId)) {
              // get corresponding network client
              client = networkClients[clientId];
              // unregister from network
              unregisterNetworkClient(client);
              // announce drop
              queueCall(fireDropEvent, [client]);
              // pass-thru when there are bridge clients in this channel
              if (bridgeChannelCnts[client.channel]) {
                hostPayload.drops.push(clientData);
                shareWithHost = 1;
              }
            }

          }

          // pass event to host
          if (shareWithHost) {
            queueCall(msgHost, ['net', hostPayload]);
          }

        },

        // handle client event
        /*
        {                   [payload]
          type: 'client',
          bid: <guid>,
          msg: {           [msg]
            type: <client-type>,
            from: <guid>,
            to: [...],
            data: ...                 // optional
          }
        }
        */
        client: function (msg) {
          relayToHost(msg);
          queueCall(fireMessageEvent, [msg]);
        }

      },

      // module definition
      bridge = {
        // bridge version
        version: '0.0.0-alpha',
        // protocol version
        protocol: protocolVersion,
        // bridge id
        id: bridgeId,
        // enablement flag
        disabled: unsupported,
        // network name
        network: '',
        pendingAuths: pendingAuthReqs,
        pendingRelay: null,
        // destroy
        destroy: function () {
          var clientId;

          log('destroying bridge ' + bridgeId);

          if (!initialized || destroyed) {
            log('bridge already destroyed');
            return;
          }

          destroyed = 1;

          // disconnect remaining clients
          for (clientId in bridgeClients) {
            log('telling parent to drop client ' + clientId);
            bridgeClients[clientId].drop();
          }

          // stop listening for client commands
          unbind(scope, 'message', postMessageRouter);

          // stop monitoring localStorage
          if (isIE910) {
            unbind(doc, 'storage', ieCheckManifest);
          } else if (isIE11) {
            clearInterval(ie11ManifestTimer);
          } else {
            unbind(scope, 'storage', localStorageRouter);
          }

          // stop listening for unload
          unbind(scope, 'unload', bridge.destroy);

          // detach all events
          bridge.off();

          log('tell other bridges who has left');

          // broadcast changes immediately - skip host since we're exiting
          broadcastNetworkChanges(1);

          if (isIE) {
            if (networkClientsCnt) {
              log('removing bridge from manifest');
              delete ieManifest.b[bridgeId];
              ieSetManifest();
            } else {
              log('discarding manifest since no one else is around');
              // remove entire manifest
              ieRemoveCookie();
            }
          }

          // discard storage keys if not needed by other bridges - or for this bridge, in IE
          if (isIE || !networkClientsCnt) {
            log('removed storage keys');
            // delete localstorage keys - security'ish?
            removeStorage(msgKey);
            removeStorage(netKey);
          } else {
            log('did not remove storage keys');
          }

          // inform host we're gone - send some kind of code
          msgHost('die', 123);
          log('exit: coookie = "' + document.cookie + '"');
          log('exit: storage length ' + localStorage.length);
        },
        // parse token
        init: function (token) {
          var pos = protocolVersion.length;

          // exit now if already initialized on unsupported platform
          if (initialized || destroyed || unsupported) {
            return;
          }

          // in case this method gets invoked after listening for first ping
          unbind(scope, 'message', handleFirstPing);

          if (
            !isFullString(token) ||
            token.substring(0, pos) != protocolVersion
          ) {
            next(function () {
              bridge.fire(ERROR_EVENT, 'invalid initialization token');
            });
            return;
          }

          // account for first backtick
          pos++;

          // get speaker key
          speakerKey = token.substring(pos, token.indexOf(backtick, pos));
          pos += speakerKey.length + 1;

          // using custom check because IE is unicorns
          if (isNaN(speakerKey)) {
          // if (typeof isNaN == 'undefined' ? !/^[0-9\.]+$/.test(speakerKey) : isNaN(speakerKey)) {
            return;
          }

          speakerKey *= 1;

          // get bridge network name/id
          bridgeNetworkName = token.substring(pos, token.indexOf(backtick, pos));
          // get bridge network name/id
          if (!bridgeNetworkName) {
            return;
          }

          // set cipher to remainder of bootstrap token
          cipher.cipher(token.substring(pos + bridgeNetworkName.length + 1));

          // exit if cipher fails - testing with bridge id
          if (cipher.decode(cipher.encode(bridgeNetworkName)) !== bridgeNetworkName) {
            return;
          }

          // all tests passed!
          initialized = 1;

          // capture bridge network
          bridge.network = bridgeNetworkName;

          // create string parser if we can't post objects
          if (!canPostObjects) {
            r_validClientMsg = new RegExp('^{"key":' + speakerKey + ',"mid":"[0-9a-f-]{36}","type":".+?","msg":.+}$');
          }


          // randomly delay network bootstrap, to reduce startup lag/collision
          // thx https://github.com/mafintosh !
          setTimeout(function () {
            // exit if already destroyed
            if (destroyed) {
              return;
            }

            // listen for client commands
            bind(scope, 'message', postMessageRouter);

            // monitor localStorage
            if (isIE910) {
              // check manifest when localstorage fires
              bind(doc, 'storage', ieCheckManifest);
            } else if (isIE11) {
              // watch manifest
              ie11ManifestTimer = setInterval(ieCheckManifest, ieMsgDelay + 10);
            } else {
              // otherwise listen as normal
              bind(scope, 'storage', localStorageRouter);
            }

            // note that we're initialized
            bridge.fire(INITIALIZE_EVENT);

            if (destroyed) {
              return;
            }

            // listen for when the page closes
            bind(scope, 'unload', bridge.destroy);
            log('INIT: told host we\'re ready to talk!');
            // tell host we're ready
            msgHost('ready', origin);
          }, (isIE ? 30 : 0) + Math.round(mathRandom() * 75));
        },
        on: function (evt, callback) {
          var me = this;

          if (
            isFullString(evt) &&
            typeof callback == 'function'
          ) {
            if (!protoHas.call(me, '_evts')) {
              // init events hash
              me._evts = {};
            }
            if (!protoHas.call(me._evts, evt)) {
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

          if (!protoHas.call(me, '_evts') || !argLn) {
            // reset if clearing all events
            me._evts = {};
          } else if (
            isFullString(evt) &&
            protoHas.call(me._evts, evt)
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
        fire: function (evt) {
          var
            me = this,
            params,
            cbs,
            cbLn,
            cbIdx,
            callbackInvoker;

          if (
            isFullString(evt) &&
            protoHas.call(me, '_evts') &&
            protoHas.call(me._evts, evt) &&
            (cbLn = (cbs = me._evts[evt]).length)
          ) {
            params = protoSlice.call(arguments, 1);
            if (params.length) {
              callbackInvoker = function (cb) {
                cb.apply(me, params);
              };
            } else {
              callbackInvoker = function (cb) {
                cb.call(me);
              };
            }
            for (cbIdx = 0; cbIdx < cbLn; cbIdx++) {
              callbackInvoker(cbs[cbIdx]);
            }
          }

          return me;
        }
      }
    ;

    // exit now if platform is unsupported
    if (unsupported) {
      // exiting before inheritance chains have been created
      // this OK since the whole thing shouldn't be used and ups performance
      return bridge;
    }

    // UTILITY FUNCTIONS

    // shallow object merge
    function mix(base) {
      var
        argIdx = 1,
        source,
        member;

      for (; source = arguments[argIdx]; argIdx++) {
        for (member in source) {
          if (protoHas.call(source, member)) {
            base[member] = source[member];
          }
        }
      }
      return base;
    }

    // return date timestamp
    function now() {
      return new Date();
    }

    // returns true when one of the keys is not in the given object
    function hasNotAtLeastOneKey(obj, keys) {
      var ln = keys.length;

      if (obj && ln) {
        while (ln--) {
          if (!protoHas.call(obj, keys[ln])) {
            return 1;
          }
        }
      }
    }

    // returns true when one of the keys is in the given object
    function hasAtLeastOneKey(obj, keys) {
      var ln = keys.length;

      if (obj && ln) {
        while (ln--) {
          if (protoHas.call(obj, keys[ln])) {
            return 1;
          }
        }
      }
    }

    // generates a guaranteed unique id
    function guid() {
      return guidPattern.replace(rxp_guid, guid_helper);
    }

    // guid helper, for replacing characters
    function guid_helper (c) {
      var
        r = mathRandom() * 16 | 0,
        v = c == 'x' ? r : (r & 0x3 | 0x8);

      return v.toString(16);
    }

    // quick check for non-zero length strings
    function isFullString(value) {
      return value && typeof value == 'string';
    }

    // return a random number of random characters, excluding "{", "|", and "}"
    function randomPadding() {
      var
        spaces = [],
        count = ~~(mathRandom() * 40);

      while (count--) {
        spaces.push(stringfromCharCode(~~(mathRandom() * 90)));
      }
      return spaces.join('');
    }

    // FUNCTIONS

    // scan manifest for message key updates
    function ieCheckManifest() {
      var
        bid,
        newTick,
        newBridge,
        manifestTicks,
        bValue,
        routedMsg,
        updateManifest,
        i,
        j
      ;

      if (arguments.length && arguments[0].type == 'storage') {
        log('checking manifest due to storage event');
      } else {
        log('periodic cookie check');
      }

      // get latest manifest
      ieGetManifest();

      // alias manifest message tick tracker
      manifestTicks = ieManifest.m;

      // remove this bridge as a tracker
      delete manifestTicks[bridgeId];

      log('Inspecting ' + Object.keys(manifestTicks).length + ' bridge ticks');

      for (bid in manifestTicks) {
        log('comparing ' + manifestTicks[bid] + ' in manifest with ' + ieBridgeTicks[bid] + ' in memory for ' + bid.substr(0,4));

        // skip inherited props
        if (!protoHas.call(manifestTicks, bid)) {
          continue;
        }

        // coerce manifest tick now
        newTick =  +manifestTicks[bid];

        if (
          // unknown bridge or bridge with no peers,
          (newBridge = !protoHas.call(ieBridgeTicks, bid) || !protoHas.call(ieBridgeIds, bid) || !ieBridgeIds[bid]) ||
          // greater than last known message for this bridge
          /*
            We could check to ensure the tick has incremented one "unit"
            If more than one, then we could kill the bridge, in order
            to reset everything?
          */
          newTick > ieBridgeTicks[bid]
        ) {
          // if new bridge or no known peers...
          if (newBridge) {
            // // if bridge is not in bridges...
            // if (!protoHas.call(ieManifest.b, bid)) {
            //   log('removing bridge since its not in register' + bid.substr(0,4));
            //   // remove from manifest
            //   delete ieManifest.m[bid];
            //   // flag to update manifest
            //   updateManifest = 1;
            //   // skip this bridge ticker
            //   continue;
            // }

            log('mapping new bridge! '  + bid.substr(0,4));
            // get client map for bridge
            newBridge = ieGetBridgeClientMapAsString(bid);
            if (newBridge) {
              try {
                // parse map into json objects
                newBridge = JSONparse(newBridge);
              } catch(e) {
                newBridge = 0;
              }
              // add network clients
              if (newBridge) {
                log('network peers found via bridge ' + bid.substr(0,4));
                // tally number of peers from bridge
                ieBridgeIds[bid] = 0;
                addNewNetworkClients(newBridge);
              }
            }
          } else {
            log('existing bridge has ' + ieBridgeIds[bid] + ' peers');
          }

          // update/capture tick
          ieBridgeTicks[bid] = newTick;

          // retrieve this bridge's message key
          bValue = getStorage(bid + msgKeySuffix);

          log('bridge ' + bid.substring(0,4) + ' has a message!');

          // skip if it isn't an prefixed array
          if (!ie_r_validInitialStorageEvent.test(bValue)) {
            log('uh oh! message does not look like an valid grouped storage message -> "' + bValue + '"');
            // if new bridge check again in 5 ms?
            continue;
          } /* else throw? */

          // extract array
          bValue = bValue.substr(bValue.indexOf('['));

          // attempt to parse array
          try {
            bValue = JSONparse(bValue);
          } catch (e) {
            log('message could not be parsed!');
            continue;
          }

          // process array of values
          if (isArray(bValue)) {
            j = bValue.length;
            // log('handling ' + j + ' messages');
            // update throttle marker, so we don't respond too quickly
            if (!routedMsg) {
              routedMsg = 1;
              ieLastMsgTime = now();
            }
            for (i = 0; i < j; i++) {
              log('routing message ' + (i + 1) + ': ' + JSONstringify(bValue[i]));
              // pass to router for individual controller handling
              localStorageRouter({
                key: msgKey,
                newValue: bValue[i]
              });
            }
          } else {
            log('message was skipped since it is not an array');
          }
        } else {
          log('no change to bridge ' + bid.substr(0,4) + ' with ' + ieBridgeIds[bid] + ' peers');
        }
        if (updateManifest) {
          ieSetManifest();
        }
      }
    }

    function ieGetBridgeClientMapAsString(bid) {
      var clientMap = getStorage(bid + netKeySuffix);
      // if expected type and more than "[]"...
      if (isFullString(clientMap) && clientMap.length > 2) {
        // return stringified array
        return clientMap;
      } /* else {
        // this map is invalid... do we remove this network map, etc?
      }*/
      return '';
    }

    // update ieManifest from document.cookie
    function ieGetManifest() {
      var
        cookieStr = doc.cookie,
        startPos = cookieStr.indexOf(ieCookieNameStr),
        endPos,
        parsed,
        bids,
        msgs,
        hasDeadBridge,
        deadBridges = {},
        bid,
        clientId,
        client,
        droppedNetworkClients
      ;
      log('cookie check!' + cookieStr);
      if (~startPos) {
        endPos = cookieStr.indexOf(';', startPos);
        cookieStr = cookieStr.substring(startPos + ieCookieNameStrLength, ~endPos ? endPos : undefined);
        if (cookieStr) {
          try {
            ieManifest = JSON.parse(cookieStr);
            parsed = 1;
          } catch (e) {}
        }
      }
      if (parsed) {
        bids = ieManifest.b;
        msgs = ieManifest.m;

        // remove dead bridges from messages
        for (bid in msgs) {
          // discard message ticker when bid is not sanctioned
          if (!protoHas.call(bids, bid) && protoHas.call(msgs, bid)) {
            log('removing expired bridge ' + bid);
            hasDeadBridge = 1;
            // capture dead bridge id
            deadBridges[bid] = 1;
          }
        }
        // remove orphaned bridges
        for (bid in ieBridgeIds) {
          // if bridge is no longer in the manifest
          if (!protoHas.call(bids, bid) && protoHas.call(ieBridgeIds, bid)) {
            log('removing orphaned bridge ' + bid);
            hasDeadBridge = 1;
            // capture dead bridge id
            deadBridges[bid] = 1;
          }
        }
        // save clean up changes now
        if (hasDeadBridge) {

          // init payload to share with host
          droppedNetworkClients = [];

          for (bid in deadBridges) {
            if (protoHas.call(deadBridges, bid)) {
              // remove from ieBridgeIds
              delete ieBridgeIds[bid];
              // remove from manifest messages
              delete msgs[bid];
              // discard clients from this bridge
              for (clientId in networkClients) {
                if (
                  protoHas.call(networkClients, clientId) &&
                  (client = networkClients[clientId]).bid == bid
                ) {

                  // should be easy as client.unregister()

                  unregisterNetworkClient(client);

                  // capture client when there are bridge clients in this channel
                  if (bridgeChannelCnts[client.channel]) {
                    droppedNetworkClients.push(client);
                  }

                }
              }
              // remove storage keys - just in case
              removeStorage(bid + netKeySuffix);
              removeStorage(bid + msgKeySuffix);
            }
          }
          // save manifest changes
          ieSetManifest();

          if (droppedNetworkClients.length) {
            log('informing host of clients that left' + JSONstringify(droppedNetworkClients));
            queueCall(msgHost, ['net', {drops:droppedNetworkClients, joins:[]}]);
          }
        }
      } else {
        ieManifest = {
          // bridge manifest
          b: {},
          // message manifest
          m: {}
        };
      }
    }

    function log(v) {
      // console.log(v);
    }

    function ieSetManifest() {
      // not escaping because the characters are safe
      // and we want to minimize cookie size
      doc.cookie = ieCookieNameStr + JSON.stringify(ieManifest) + ieCookiePathStr;
      // update last set time
      ieLastMsgTime = now();
    }

    function ieRemoveCookie() {
      doc.cookie = ieCookieRemoveStr;
    }

    // send array-buffer of network messages
    function ieSendNetworkBuffer() {
      if (!ieNetworkBuffer.length) {
        return;
      }

      // update msg tick for this bridge
      ieGetManifest();
      ieManifest.b[bridgeId] = 1;
      ieManifest.m[bridgeId] = ++ieTickValue;
      ieSetManifest();

      // update local storage
      sendStorageMessage(ieNetworkBuffer);

      // empty buffer
      ieNetworkBuffer.length = 0;
    }

    function runCall(fnc, args) {
      if (args) {
        fnc.apply(0, args);
      } else {
        fnc();
      }
    }

    /*
    Executes queue of calls, long as:
      1. the network buffer is empty, or
      2. the netwrok buffer is not empty and the last message was sent more than 50ms ago
    */
    function ieRunQueue() {
      var
        runTime = now(),
        timeRemaining = runTime - ieLastMsgTime,
        i = 0,
        j = ieCallQueue.length
      ;

      clearTimeout(ieMsgTimer);

      // exit if last call was too recent- unless we're destroyed
      if (!destroyed && timeRemaining < ieMsgDelay) {
        // log('not calling queue because not enough time has passed (' + timeRemaining + ' < ' + ieMsgDelay + ') last time was ' + ieLastMsgTime);
        ieMsgTimer = setTimeout(ieRunQueue, ieMsgDelay - timeRemaining + 3);
        return;
      }

      // is this needed?
      ieMsgTimer = 0;

      // log('executing queue of ' + ieCallQueue.length + ' calls');

      // execute call queue
      for (; i < j; i++) {
        runCall.apply(0, ieCallQueue[i]);
      }

      // clear call queue
      ieCallQueue.length = 0;
      // capture last send time
      ieLastMsgTime = runTime;
    }

    function resolveNetworkChannel(channelName) {
      if (!protoHas.call(networkChannels, channelName)) {
        networkChannels[channelName] = {};
        networkChannelCnts[channelName] = 0;
      }
      return networkChannels[channelName];
    }

    function resolveBridgeChannel(channelName) {
      if (!protoHas.call(bridgeChannels, channelName)) {
        bridgeChannels[channelName] = {};
        bridgeChannelCnts[channelName] = 0;
      }
      return bridgeChannels[channelName];
    }

    function wrapStorageMessage(type, msg) {
      return {
        type: type,
        bid: bridgeId,
        msg: msg
      };
    }

    // share message with network
    function sendStorageMessage(payload) {
      setStorage(msgKey, storagePfx + lastStamp + JSONstringify(payload));
    }

    function setStorage(key, val) {
      LS.setItem(key, val);
    }

    function getStorage(key) {
      return LS.getItem(key);
    }

    function removeStorage(key) {
      LS.removeItem(key);
    }

    function relayToHost(msg, channelName) {
      var
        viaNetwork = 0,
        fromId,
        bridgeCnt;

      if (!channelName) {
        fromId = msg.from;
        if (!protoHas.call(networkClients, fromId)) {
          // don't relay unknown network clients
          return;
        }
        channelName = networkClients[msg.from].channel;
        viaNetwork = !protoHas.call(bridgeClients, fromId);
      }
      // announce message event - allow routines to alter the message

      // announce joins & drops now, in case a (network) client is supposed to receive this relay
      broadcastNetworkChanges();
      bridgeCnt = bridgeChannelCnts[channelName];
      // send to host when a target client is local or unspecified
      if (
        (
          !msg.to &&
          (
            (viaNetwork && bridgeCnt) ||
            (!viaNetwork && bridgeCnt > 1)
          )
        ) ||
        (
          msg.to &&
          hasBridgeClient(msg.to)
        )
      ) {
        queueCall(msgHost, ['client', msg]);
      }
    }

    // send message to host
    function msgHost(type, msg) {
      postMessage(
        // protocol message
        [
          // protocol version
          protocolVersion,
          // network id
          bridgeNetworkName,
          // encode message
          cipher.encode(
            // random head padding
            randomPadding() +
            // json the msg
            JSONstringify({
              mid: guid(),
              type: type,
              sent: now(),
              msg: msg
            }) +
            // random tail padding
            randomPadding()
          )
        ]
        // no origin needed
      );
      // alter cipher per message
      cipher.shift++;
    }

    function hasBridgeClient(ids) {
      var i = ids.length;
      while (i--) {
        if (protoHas.call(bridgeClients, ids[i])) {
          return 1;
        }
      }
      return 0;
    }

    // ensures request methods are only invoked once
    function wrapRequestMethods(req) {
      var
        allowFn = req.allow,
        denyFn = req.deny,
        ignoreFn = req.ignore,
        undecided = 1;

      req.allow = function () {
        if (undecided) {
          undecided = 0;
          callFncArgs(req, denyFn, arguments);
          return true;
        }
        return false;
      };

      req.deny = function () {
        if (undecided) {
          undecided = 0;
          callFncArgs(req, allowFn, arguments);
          return true;
        }
        return false;
      };

      req.ignore = function () {
        if (undecided) {
          undecided = 0;
          callFncArgs(req, ignoreFn, arguments);
          return true;
        }
        return false;
      };

    }

    // supports #wrapRequestMethods
    function callFncArgs(obj, fnc, args) {
      if (args.length) {
        return fnc.apply(obj, args);
      }
      return fnc.call(obj);
    }

    // allows handling next client event
    function unlockAndRunQueue() {
      // unlock queue
      relayQueueLocked = 0;
      // resume queue next
      next(runRelayQueue);
    }

    // process next client event
    function runRelayQueue() {
      var request;

      // exit if queue is closed or there are no messages to relay
      if (relayQueueLocked || !relayQueue.length) {
        return;
      }

      // lock queue
      relayQueueLocked = 1;
      // take command off queue and create client message request
      request = new RelayRequest(relayQueue.shift());
      if (
        !protoHas.call(bridge, '_evts') ||
        !protoHas.call(bridge._evts, RELAY_EVENT) ||
        !bridge._evts[RELAY_EVENT].length
      ) {
        request.allow();
      } else {
        wrapRequestMethods(request);
        // add as pending relay
        bridge.pendingRelay = request;
        // announce client event request
        bridge.fire(RELAY_EVENT, request);
      }
    }

    function fireJoinEvent(client) {
      // only fire if still joining
      if (protoHas.call(joinQueue, client.id)) {
        bridge.fire(JOIN_EVENT, client);
      }
    }

    function fireDropEvent(client) {
      bridge.fire(DROP_EVENT, client);
    }

    function fireMessageEvent(msg) {
      bridge.fire(MSG_EVENT, msg);
    }

    // add client to given (drop/join) queue and run queue later
    function queueNetworkChange(client, queue) {
      // log('network change queued for client ' + client.id.substr(0,4));
      queue[client.id] = client;
      clearTimeout(networkChangeTimer);
      // allow 5ms of additional client activity
      // so we can batch network changes and reduce storage events
      networkChangeTimer = setTimeout(broadcastNetworkChanges, 5);
    }

    // share client drops & joins with network
    function broadcastNetworkChanges(skipHost) {
      var
        jq = joinQueue,
        dq = dropQueue,
        joins = [],
        drops = [],
        clientId,
        client,
        channelId,
        channel,
        channels = isIE ? bridgeChannels : networkChannels,
        payload,
        clients;

      // clear timer
      clearTimeout(networkChangeTimer);

      // reset queues
      joinQueue = {};
      dropQueue = {};

      for (clientId in jq) {
        client = jq[clientId];
        joins.push(client);
        fireJoinEvent(client);
      }
      for (clientId in dq) {
        client = dq[clientId];
        drops.push({
          id: clientId,
          channel: client.channel
        });
        fireDropEvent(client);
      }

      log('broadcastNetworkChanges');

      // only notify when there are joins or drops
      if (joins.length || drops.length) {
        log('added ' + joins.length + ' and dropped ' + drops.length + ' peers');
        // convert channels to arrays
        clients = [];
        for (channelId in channels) {
          if (protoHas.call(channels, channelId)) {
            channel = channels[channelId];
            for (clientId in channel) {
              if (protoHas.call(channel, clientId)) {
                clients.push(channel[clientId]);
              }
            }
          }
        }
        // log('updating "net" key map');
        // store channels directly
        setStorage(netKey, JSONstringify(clients));

        payload = {
          joins: joins,
          drops: drops
        };

        queueNetworkRelay('net', payload);
        if (!skipHost) {
          queueCall(msgHost, ['net', payload]);
        }
      } else {
        log('no client changes to share');
      }
    }

    // removes pending auth from stack
    function removePendingAuthRequest(request) {
      var clientId = request.client.id;

      if (protoHas.call(pendingAuthReqs, clientId)) {
        delete pendingAuthReqs[clientId];
      }
    }

    // add client to network indexes
    function registerNetworkClient(client, networkChannel) {
      var
        clientId = client.id,
        channelName = client.channel;

      // add to network client and channel indexes
      networkClients[clientId] =
      (networkChannel || resolveNetworkChannel(channelName))[clientId] =
        client;

      // increment network channel tally
      networkChannelCnts[channelName]++;
      // increment network client tally
      networkClientsCnt++;

      return client;
    }

    // add client to bridge indexes
    function registerBridgeClient(client, bridgeChannel) {
      var
        clientId = client.id,
        channelName = client.channel;

      // add to network indexes
      registerNetworkClient(client);

      // add to bridge client and channel indexes
      bridgeClients[clientId] =
      (bridgeChannel || resolveBridgeChannel(channelName))[clientId] =
        client;

      // increment network channel tally
      bridgeChannelCnts[channelName]++;
      // increment bridge client tally
      bridgeClientsCnt++;

    }

    // remove client from network indexes
    function unregisterNetworkClient(client) {
      var
        channelName = client.channel,
        clientId = client.id;

      // remove from network index
      delete networkClients[clientId];
      // decrement network client tally
      networkClientsCnt--;

      // if this is the last client in the channel
      if (networkChannelCnts[channelName] == 1) {
        // remove channel
        delete networkChannels[channelName];
        // remove channel tally
        delete networkChannelCnts[channelName];
      } else {
        // remove client from channel
        delete networkChannels[channelName][clientId];
        // decrement channel tally
        networkChannelCnts[channelName]--;
      }

    }

    // remove client from bridge indexes
    function unregisterBridgeClient(client) {
      var
        clientId = client.id,
        channelName = client.channel;

      // remove from network indexes
      // unregisterNetworkClient(client);

      // remove from bridge client index
      delete bridgeClients[clientId];
      // remove from joinQueue - just in case
      delete joinQueue[clientId];

      // if this is the last client in the bridge channel
      if (bridgeChannelCnts[channelName] == 1) {
        // remove bridge group
        delete bridgeChannels[channelName];
        // remove bridge group count tally
        delete bridgeChannelCnts[channelName];
      } else {
        // remove from bridge channel group
        delete bridgeChannels[channelName][clientId];
        // decremenet bridge channel tally
        bridgeChannelCnts[channelName]--;
      }
    }

    // register new network clients
    function addNewNetworkClients(clients) {
      var
        ln = clients.length,
        client
      ;
      while (ln--) {
        client = clients[ln];
        // only register add unknown clients
        if (!protoHas.call(networkClients, client.id)) {
          log('registering existing network client: ' + client.id);
          registerNetworkClient(new NetworkClient(client));
        }
      }
    }

    // route "message" events
    function postMessageRouter(evt) {
      var
        cmd = evt.data,
        cmdType = typeof cmd,
        cmdName,
        mid,
        securedByRegExp = 0,
        code = CLIENT_RSP_MISSING_COMMAND;

      // capture to cache-bust db changes
      lastStamp = evt.timeStamp || now() * 1;

      // parser
      if (
        !canPostObjects &&
        cmdType == 'string'
      ) {
        // assess json before parsing
        if (r_validClientMsg.test(cmd)) {
          try {
            cmd = JSONparse(cmd);
            securedByRegExp = 1;
          } catch (e) {
            // bad json
            return;
          }
        } else {
          // malformed msg
          return;
        }
      } else if (cmdType !== 'object') {
        // bad msg type
        return;
      }

      // security
      if (
        (
          // trust regexp test or...
          securedByRegExp || (
            // matches key - this supplements origin security
            cmd.key == speakerKey &&
            // has a message identifier
            isFullString((mid = cmd.mid)) &&
            // has a message
            protoHas.call(cmd, 'msg')
          )
        ) &&
        // has a known type
        protoHas.call(postMessageCommands, (cmdName = cmd.type))
      ) {
        code = postMessageCommands[cmdName](cmd, evt);
      }

      // send message receipt
      // msgHost('receipt', {
      //   mid: command.mid,
      //   code: code
      // });
    }

    // route "storage" events
    function localStorageRouter(evt) {
      var
        key = evt.key,
        msg = evt.newValue;

      // exit when not the right key
      if (key != msgKey) {
        return;
      }

      // process string
      if (typeof msg == 'string') {

        if (!r_validStorageEvent.test(msg)) {
          // string is invalid
          return;
        }

        // extract "body" of message
        msg = msg.substring(msg.indexOf('{'));

        // exit on parse error
        try {
          msg = JSONparse(msg);
        } catch (e) {
          // log?
          return;
        }

      }

      // second security
      if (
        // not an object
        typeof msg != 'object' ||
        // message has no msg property
        !protoHas.call(msg, 'msg') ||
        // there is no handler for this message
        !protoHas.call(localStorageCommands, msg.type)
      ) {
        // log?
        return;
      }

      // pass payload to command
      localStorageCommands[msg.type](msg.msg);
    }

    function handleFirstPing(evt) {
      bridge.init(evt.data);
    }

    // capture snapshot of network
    function initPeers() {
      var
        allClients,
        bmap,
        bid;

      log('retreiving peer network');

      // retrieve existing clients
      if (isIE) {
        // via manifest

        // get manifest for the first time
        ieGetManifest();

        // capture current bridge ticks
        // the reference will be destroyed/cloned, when the manifest is retrieved again
        ieBridgeTicks = ieManifest.m;

        // capture current bridge ids
        // the reference will be destroyed/cloned, when the manifest is retrieved again
        ieBridgeIds = ieManifest.b;

        // prep to build clients JSON string
        allClients = [];
        // merge network maps from each bridge
        for (bid in ieManifest.b) {
          if (protoHas.call(ieManifest.b, bid)) {
            // get json string and remove array brackets
            bmap = ieGetBridgeClientMapAsString(bid).slice(1,-1);
            if (bmap) {
              // add if valid
              allClients.push(bmap);
            }
          }
        }
        // join and wrap in expected array brackets
        allClients = '[' + allClients.join(',') + ']';

      } else {
        // via storage

        // get network channels
        allClients = getStorage(netKey);
      }

      // create client instances
      if (isFullString(allClients) && allClients.length > 2) {
        try {
          allClients = JSONparse(allClients);
        } catch (e) {
          if (isIE) {
            /*
              one of the storage keys was malformed.
              what do we do?

              1. do we kill the offending storage key - so no other bridge goes through this?
              2. message the bridge and tell them to update it themselves?
              3. tell other bridges to drop those clients?
              4. all of the above??
            */
            log('init: could not parse clients list from cookie');
          } else {
            LS.removeItem(netKey);
            // exit? fail? log?
          }
        }

        // initilialize client instances
        if (isArray(allClients)) {
          log('adding ' + allClients.length + ' peers');
          addNewNetworkClients(allClients);
        } else {
          log('no peers on network');
        }
      }


      if (!isIE910) {
        setInterval(function () {
          if (now() - ieLastMsgTime > 95) {
            ieCheckManifest();
            if (ieNetworkBuffer.length) {
              // log('periodic check found ' + ieNetworkBuffer.length + ' items  in the queue');
              ieRunQueue();
            }
          }
        }, 100);
      }

      initedPeers = 1;
    }

    // manage request to authorize clients
    function AuthRequest(clientData, mid) {
      var me = this;

      me.client = clientData;
      me.credentials = clientData.creds;
      me.mid = mid;

      // remove creds from clientData
      delete clientData.creds;
    }

    mix(AuthRequest.prototype, {

      // add client to network
      allow: function () {
        var
          me = this,
          clientData = me.client,
          client,
          clientId = clientData.id;

        removePendingAuthRequest(me);

        // if first lookup of peers
        if (!initedPeers) {
          initPeers();
        }

        // respond to auth request and send existing peers
        msgHost('auth', {
          id: clientId,
          ok: true,
          peers: resolveNetworkChannel(clientData.channel)
        });

        client = new BridgeClient(clientData);

        // this should be this simple
        // client.join();

        // immediatley track this client
        registerBridgeClient(client);

        // buffer announcing this client to bridges
        queueNetworkChange(client, joinQueue);
      },

      // decline authorization
      deny: function (reason) {
        var me = this;

        removePendingAuthRequest(me);

        msgHost('auth', {
          id: me.client.id,
          ok: false,
          code: typeof reason == 'string' ? reason : ''
        });

      },

      // ignore authorization
      ignore: function () {
        removePendingAuthRequest(this);
      }

    });

    // manage request to relay client events
    function RelayRequest(pkg) {
      var me = this;
      me.sent = pkg.sent;
      me.msg = pkg.msg;
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
          networkPeerCount = networkChannelCnts[channelName];

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
            queueNetworkRelay('client', msg);
            relayed = 1;
          }

          // if anything got relayed
          if (relayed) {
            queueCall(fireMessageEvent, [msg]);
          }

        }
        unlockAndRunQueue();
      },

      deny: unlockAndRunQueue,

      ignore: unlockAndRunQueue

    });

    // basic client
    function Client(clientData) {
      var me = this;

      if (clientData) {
        me.id = clientData.id;
        me.channel = clientData.channel;
        me.origin = clientData.origin;
      }

    }

    mix(Client.prototype, {

      // remove client from network
      drop: function () {
        var
          me = this,
          clientId = me.id;

        // exit if not a client
        if (protoHas.call(networkClients, clientId)) {

          unregisterNetworkClient(me);

          return true;
        }
        return false;
      }

    });
    // alias for superclass calls
    protoClientDrop = Client.prototype.drop;

    // local clients, created by this bridge
    function BridgeClient(clientData) {
      var me = this;

      Client.call(me, clientData);
      me.start = now();
      me.bid = bridgeId;
    }
    BridgeClient.prototype = new Client();

    mix(BridgeClient.prototype, {

      // remove client from network & bridge
      drop: function () {
        var me = this;

        if (protoClientDrop.call(me)) {
          unregisterBridgeClient(me);
          queueNetworkChange(me, dropQueue);
          return true;
        }

        return false;
      }

    });

    // network clients, created by other bridges
    function NetworkClient(clientData) {
      var me = this;

      Client.call(me, clientData);
      me.start = new Date(clientData.start);
      me.bid = clientData.bid;
    }
    NetworkClient.prototype = new Client();

    if (isFullString(scope._subetha)) {
      // use namespaced token if present in global
      bridge.init(scope._subetha);
      // attempt to remove token??
      delete scope._subetha;
    } else {
      // await first ping
      bind(scope, 'message', handleFirstPing);
    }

    return bridge;
  }

  // initialize and expose subetha, based on the environment
  if (inAMD) {
    define(initSubEthaBridge);
  } else if (inCJS) {
    module.exports = initSubEthaBridge();
  } else if (!scope.SBridge) {
    scope.SBridge = initSubEthaBridge();
  }
}(
  typeof define == 'function', // amd test
  typeof exports != 'undefined', // node test
  localStorage, Array, Date, Math, this
);
