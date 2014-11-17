# SubEtha-Bridge

Host SubEtha clients and messages

by Bemi Faison

## Description

SubEtha-Bridge (or Bridge) is a supporting library within the SubEtha messaging architecture. A bridge routes messages between clients on the same bridge, and relays messages between bridges on the same "network" - i.e., the channel and url origin.

Bridges primarily implement the SubEtha protocol for communicating with Clients, and require zero configuration. Some security, monitoring and bootstrapping options are available.

**Note:** Please see the [SubEtha project page](https://github.com/bemson/subetha), for important background information, plus development, implementation, and security considerations.


## Usage

The Bridge module runs in a web page that is _separate_ from your application code. Bridges are loaded in iframes by the SubEtha-Client library, as needed.

### Hosting your own Bridge

Implementing your own Bridge is a simple matter of hosting a static web page. The web page should do little more than load the Bridge module, except for however you choose to customize it's behavior.

Below demonstrates a complete bridge implementation that you could host on any server.

```html
<!doctype html>
<html>
<head>
  <script src="path/to/subetha-bridge.min.js"></script>
  <title>My SubEtha-Bridge</title>
</head>
</html>
```

#### Connecting to your Bridge

If the url to your bridge were `http://my.site.com/bridge.html`, clients could then connect to it in their applications, like so:

```js
// open a channel on your bridge
var myAppClient = new Subetha.Client();
myAppClient.open('some-channel@my.site.com/bridge.html');
```

If applications plan to use several clients with your bridge, they might set and use a convenient alias, instead.

```js
// define an alias to your bridge url
Subetha.urls.mybridge = 'my.site.com/bridge.html';

// open a channel using an alias
var myAppClient = new Subetha.Client();
myAppClient.open('some-channel@mybridge');
```

#### Bootstrapping Asynchronous Bridges

The Bridge module has a bootstrap process that involves capturing the _first_ [message](http://help.dottoro.com/ljjqtjsj.php) event - sent via postMessage, from the SubEtha-Client in the parent window. It is **strongly** recommended that you load the Bridge module _synchronously_ (via a SCRIPT tag, or otherwise, _before_ the DOM is ready). If you do load the Bridge module asynchronously, you **must** capture the first message event and pass it's data, manually.

Below demonstrates loading the Bridge module with require.js and capturing the first message event. It ensures the bridge is only initialized when both it and the event are available, regardless of load order.

```html
<!doctype html>
<html>
<head>
  <script data-main="scripts/config" src="js/require.js"></script>
  <script>
  (function () {
    var
      bridgeRef,
      bootData;

    window.addEventListener('message', function myCb(evt) {
      // remove our one-time listener
      window.removeEventListener('message', myCb);
      // capture data from first message
      bootData = evt.data;

      tryBridgeInit();
    });

    requirejs(['subetha-bridge'], function (SBridge) {
      // capture bridge reference
      bridgeRef = SBridge;

      tryBridgeInit();
    });

    //initialize bridge when both are ready
    function tryBridgeInit() {
      if (bridgeRef && bootData) {
        // start bridge with captured data
        bridgeRef.init(bootData);
      }
    }
  })();
  </script>
</head>
</html>
```

**Note:** The above leaves `scripts/config` to configure the "subetha-bridge" module path and dependencies.

### Handling Client Requests

Bridges handle two types of client requests: authentication requests, and message-relay requests. These requests are accepted by default, such that any client may join a channel and send any message.

To handle requests manually, simply subscribe to the "auth" and/or "relay" events. Callbacks receive a _request object_, which represents the suspended state of a request. Requests may be _answered_ asynchronously, but can only be answered once.


```js
// handle client authentication requests
SBridge.on('auth', function (req) {
  // perform logic now and/or handle this request later
});

// handle message relay requests
SBridge.on('relay', function (req) {
  // perform logic now and/or handle this request later
});
```

To _answer_ a request invoke it's `#allow()`, `#deny()`, or `#ignore()` method. The first call to any method will return `true`, but once handled these methods (do nothing and) return `false`.

```js
SBridge.on('auth', function (req) {
  if (req.client.origin != 'http://example.com') {
    // the first method called, wins
    req.deny(); // returns `true`
  }
  // does nothing if already denied
  req.allow(); // returns `false`
});
```

**Note:** The same request object is passed to all callbacks. If using multiple callbacks for an event, ensure only - and, at least - one handles the request object.

To restore the default behavior, remove _all_ subscriptions to the given event type. Invoke `#off()`, passing only the event type.

```js
// re-enable default handling of authentication requests
SBridge.off('auth');

// re-enable default handling of message-relay requests
SBridge.off('relay');
```

#### Authenticating Clients

Authentication-requests may be handled in any order, and are stored in the `SBridge.pendingAuths` hash until processed. If your bridge employs some form of authorization, requests expose any credentials given by the client, in a `.credentials` array. (An empty array, means no credentials were sent.)

```js
SBridge.on('auth', function (req) {
  if (req.credentials.length) {
    // verify credentials, now or later
  } else {
    req.deny();
  }
});
```

#### Relaying Messages

Message-relay requests can only be handled in the order they are received. When a request is suspended, it is passed to subscribers of the "relay" event, and set in the `SBridge.pendingRelay` namespace.

It's important to consider latency, when processing a relay request. More message-relay requests will pile up as you perform your logic, which can reduce perceived performance of your bridge. Try to handle message-relay requests immediately, instead of asynchronously.

Below, demonstrates logic that prevents broadcast messages - messages without a recipient.

```js
SBridge.on('relay', function (req) {
  // the message has no client id in the "to" field
  if (!req.msg.to) {
    req.deny();
  } else {
    req.allow();
  }
});
```

### Monitoring Bridge Activity

The following events are available for you to observe, on the Bridge module directly.

 * **initialize** Fired when the Bridge is awaiting client messages.
 * **join** Fired when a client has joined the network. The arriving client is passed to callbacks.
 * **drop** Fired when a client has exited the network. The departed client is passed to callbacks.
 * **message** Fired when a message is relayed. The delivered message is passed to callbacks.

**Note:** Unlike the SubEtha-Client module, Bridge events are not prefixed.

Below demonstrates logic that observes when a new client has been authenticated by the current bridge.

```js
SBridge.on('join', function (client) {
  if (SBridge.id == client.bid) {
    // do something, now that a client joined via this bridge
  }
});
```


## API

Below is reference documentation for the SubEtha-Bridge module.

### SBridge

A singleton, representing the client authorization and message routing logic for the window.

##### Bridge events

The bridge fires the following events.

  * **relay** - Triggered before a message is relayed. Subscribing to this event requires responding to the relay-request.
    * `request` - An object representing the suspended request.
  * **auth** - Triggered when a client attempts to use this bridge to join the network.
    * `request` - An object representing the suspended request.
  * **join** - Triggered when a client joins the network.
    * `client` - A reference to the client that recently joined the network.
  * **drop** - Triggered when a client leaves the network.
    * `client` - A reference to the client that recently left the network.
  * **message** - Triggered when a client message is relayed.
    * `msg` - The message relayed on the network.

### SBridge::destroy()

End handling network clients and messages. You can not reuse the bridge once destroyed.

```
SBridge.destroy();
```

### SBridge::fire()

Triggers callbacks, subscribed to this event.

```
SBridge.fire(event [, args, ... ]);
```

   * **event**: _(string)_ The event to trigger.
   * **args**: _(Mix)_ Remaining arguments that should be passed to all attached callbacks.

### SBridge::init()

Begin handling network clients and messages.

```
SBridge.init(token);
```

  * **token**: _(string)_ A serialized string of parameters needed to bootstrap the SBridge singleton.

This method simply exits if the bridge has already been initialized.

### SBridge::off()

Unsubscribe callback(s) from an event. When invoked with no arguments, all subscriptions are removed.

```
SBridge.off([event [, callback ]]);
```

   * **event**: _(string)_ The event to unsubscribe. When omitted, all event subscribers are removed.
   * **callback**: _(function)_ The callback to detach from this event. When omitted, all callbacks are detached from this event.

### SBridge::on()

Subscribe a callback to an event.

```
SBridge.on(event, callback);
```

   * **event**: _(string)_ An arbitrary event name.
   * **callback**: _(function)_ A callback to invoke when the event is fires.

### Sbridge::disabled

Indicates when the bridge is incompatible with the runtime environment.

### Sbridge::id

A hash to uniquely identify this bridge.

### SBridge::network

The name of the network, as prescribed by the bootstrap token.

### SBridge::pendingRelay

The last pending message relay request object. If no relay is pending, the value is `null`.

### SBridge::pendingAuths

Hash of pending authorization request objects. Keys are of clients waiting to gain access.

### SBridge::protocol

The [SemVer](http://semver.org) compatible version of the SubEtha protocol supported by this module.

### SBridge::version

The [SemVer](http://semver.org) compatible version of this module.


## Installation

SubEtha-Bridge works within, and is intended for, modern JavaScript browsers. It is available on [bower](http://bower.io/search/?q=subetha-bridge), [component](http://component.github.io/) and [npm](https://www.npmjs.org/package/subetha-bridge) as a [CommonJS](http://wiki.commonjs.org/wiki/CommonJS) or [AMD](http://wiki.commonjs.org/wiki/Modules/AsynchronousDefinition) module.

If SubEtha-Bridge isn't compatible with your favorite runtime, please file an issue or pull-request (preferred).

### Dependencies

SubEtha-Bridge depends on the following modules:

  * [Morus](https://github.com/bemson/morus)

SubEtha-Bridge also uses the following ECMAScript 5 and HTML 5 features:

  * [JSON.parse](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/JSON/parse)
  * [JSON.stringify](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/JSON/stringify)
  * [localStorage](http://diveintohtml5.info/storage.html)
  * [postMessage](https://developer.mozilla.org/en-US/docs/Web/API/Window.postMessage)

You will need to implement shims for these browser features in unsupported environments. Note however that postMessage and localStorage shims will only allow this module to run without errors, not work as expected.

### Web Browsers

Use a `<SCRIPT>` tag to load the _subetha-bridge.min.js_ file in your web page. The file includes all module dependencies, for your convenience. Doing so, adds `SBridge` to the global scope.

```html
  <script type="text/javascript" src="path/to/subetha-bridge.min.js"></script>
  <script type="text/javascript">
    // ... SubEtha-Bridge dependent code ...
  </script>
```

**Note:** The minified file was compressed by [Closure Compiler](http://closure-compiler.appspot.com/).

### Package Managers

  * `npm install subetha-bridge`
  * `component install bemson/subetha-bridge`
  * `bower install subetha-bridge`

### AMD

Assuming you have a [require.js](http://requirejs.org/) compatible loader, configure an alias for the SubEtha-Bridge module (the term "subetha-bridge" is recommended, for consistency). The _subetha-bridge_ module exports a module namespace.

```js
require.config({
  paths: {
    'subetha-bridge': 'libs/subetha-bridge'
  }
});
```

Then require and use the module in your application code:

```js
require(['subetha-bridge'], function (SBridge) {
  // ... SubEtha Bridge dependent code ...
});
```

**Warning:** Do not load the minified file via AMD, since it includes modular dependencies that themselves export modules. Use AMD optimizers like [r.js](https://github.com/jrburke/r.js/), in order to roll-up your dependency tree.

**Note:** When loaded asynchronously, you must _manually_ bootstrap this module. (See the usage section for more details.)

## License

SubEtha-Bridge is available under the terms of the [Apache-License](http://www.apache.org/licenses/LICENSE-2.0.html).

Copyright 2014, Bemi Faison