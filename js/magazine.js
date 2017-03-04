/** vim: et:ts=4:sw=4:sts=4
 * @license RequireJS 2.1.11 Copyright (c) 2010-2014, The Dojo Foundation All Rights Reserved.
 * Available via the MIT or new BSD license.
 * see: http://github.com/jrburke/requirejs for details
 */
//Not using strict: uneven strict support in browsers, #392, and causes
//problems with requirejs.exec()/transpiler plugins that may not be strict.
/*jslint regexp: true, nomen: true, sloppy: true */
/*global window, navigator, document, importScripts, setTimeout, opera */


var requirejs, require, define;
(function (global) {
    var req, s, head, baseElement, dataMain, src,
        interactiveScript, currentlyAddingScript, mainScript, subPath,
        version = '2.1.11',
        commentRegExp = /(\/\*([\s\S]*?)\*\/|([^:]|^)\/\/(.*)$)/mg,
        cjsRequireRegExp = /[^.]\s*require\s*\(\s*["']([^'"\s]+)["']\s*\)/g,
        jsSuffixRegExp = /\.js$/,
        currDirRegExp = /^\.\//,
        op = Object.prototype,
        ostring = op.toString,
        hasOwn = op.hasOwnProperty,
        ap = Array.prototype,
        apsp = ap.splice,
        isBrowser = !!(typeof window !== 'undefined' && typeof navigator !== 'undefined' && window.document),
        isWebWorker = !isBrowser && typeof importScripts !== 'undefined',
        //PS3 indicates loaded and complete, but need to wait for complete
        //specifically. Sequence is 'loading', 'loaded', execution,
        // then 'complete'. The UA check is unfortunate, but not sure how
        //to feature test w/o causing perf issues.
        readyRegExp = isBrowser && navigator.platform === 'PLAYSTATION 3' ?
                      /^complete$/ : /^(complete|loaded)$/,
        defContextName = '_',
        //Oh the tragedy, detecting opera. See the usage of isOpera for reason.
        isOpera = typeof opera !== 'undefined' && opera.toString() === '[object Opera]',
        contexts = {},
        cfg = {},
        globalDefQueue = [],
        useInteractive = false;

    function isFunction(it) {
        return ostring.call(it) === '[object Function]';
    }

    function isArray(it) {
        return ostring.call(it) === '[object Array]';
    }

    /**
     * Helper function for iterating over an array. If the func returns
     * a true value, it will break out of the loop.
     */
    function each(ary, func) {
        if (ary) {
            var i;
            for (i = 0; i < ary.length; i += 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    /**
     * Helper function for iterating over an array backwards. If the func
     * returns a true value, it will break out of the loop.
     */
    function eachReverse(ary, func) {
        if (ary) {
            var i;
            for (i = ary.length - 1; i > -1; i -= 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    function hasProp(obj, prop) {
        return hasOwn.call(obj, prop);
    }

    function getOwn(obj, prop) {
        return hasProp(obj, prop) && obj[prop];
    }

    /**
     * Cycles over properties in an object and calls a function for each
     * property value. If the function returns a truthy value, then the
     * iteration is stopped.
     */
    function eachProp(obj, func) {
        var prop;
        for (prop in obj) {
            if (hasProp(obj, prop)) {
                if (func(obj[prop], prop)) {
                    break;
                }
            }
        }
    }

    /**
     * Simple function to mix in properties from source into target,
     * but only if target does not already have a property of the same name.
     */
    function mixin(target, source, force, deepStringMixin) {
        if (source) {
            eachProp(source, function (value, prop) {
                if (force || !hasProp(target, prop)) {
                    if (deepStringMixin && typeof value === 'object' && value &&
                        !isArray(value) && !isFunction(value) &&
                        !(value instanceof RegExp)) {

                        if (!target[prop]) {
                            target[prop] = {};
                        }
                        mixin(target[prop], value, force, deepStringMixin);
                    } else {
                        target[prop] = value;
                    }
                }
            });
        }
        return target;
    }

    //Similar to Function.prototype.bind, but the 'this' object is specified
    //first, since it is easier to read/figure out what 'this' will be.
    function bind(obj, fn) {
        return function () {
            return fn.apply(obj, arguments);
        };
    }

    function scripts() {
        return document.getElementsByTagName('script');
    }

    function defaultOnError(err) {
        throw err;
    }

    //Allow getting a global that is expressed in
    //dot notation, like 'a.b.c'.
    function getGlobal(value) {
        if (!value) {
            return value;
        }
        var g = global;
        each(value.split('.'), function (part) {
            g = g[part];
        });
        return g;
    }

    /**
     * Constructs an error with a pointer to an URL with more information.
     * @param {String} id the error ID that maps to an ID on a web page.
     * @param {String} message human readable error.
     * @param {Error} [err] the original error, if there is one.
     *
     * @returns {Error}
     */
    function makeError(id, msg, err, requireModules) {
        var e = new Error(msg + '\nhttp://requirejs.org/docs/errors.html#' + id);
        e.requireType = id;
        e.requireModules = requireModules;
        if (err) {
            e.originalError = err;
        }
        return e;
    }

    if (typeof define !== 'undefined') {
        //If a define is already in play via another AMD loader,
        //do not overwrite.
        return;
    }

    if (typeof requirejs !== 'undefined') {
        if (isFunction(requirejs)) {
            //Do not overwrite and existing requirejs instance.
            return;
        }
        cfg = requirejs;
        requirejs = undefined;
    }

    //Allow for a require config object
    if (typeof require !== 'undefined' && !isFunction(require)) {
        //assume it is a config object.
        cfg = require;
        require = undefined;
    }

    function newContext(contextName) {
        var inCheckLoaded, Module, context, handlers,
            checkLoadedTimeoutId,
            config = {
                //Defaults. Do not set a default for map
                //config to speed up normalize(), which
                //will run faster if there is no default.
                waitSeconds: 7,
                baseUrl: './',
                paths: {},
                bundles: {},
                pkgs: {},
                shim: {},
                config: {}
            },
            registry = {},
            //registry of just enabled modules, to speed
            //cycle breaking code when lots of modules
            //are registered, but not activated.
            enabledRegistry = {},
            undefEvents = {},
            defQueue = [],
            defined = {},
            urlFetched = {},
            bundlesMap = {},
            requireCounter = 1,
            unnormalizedCounter = 1;

        /**
         * Trims the . and .. from an array of path segments.
         * It will keep a leading path segment if a .. will become
         * the first path segment, to help with module name lookups,
         * which act like paths, but can be remapped. But the end result,
         * all paths that use this function should look normalized.
         * NOTE: this method MODIFIES the input array.
         * @param {Array} ary the array of path segments.
         */
        function trimDots(ary) {
            var i, part, length = ary.length;
            for (i = 0; i < length; i++) {
                part = ary[i];
                if (part === '.') {
                    ary.splice(i, 1);
                    i -= 1;
                } else if (part === '..') {
                    if (i === 1 && (ary[2] === '..' || ary[0] === '..')) {
                        //End of the line. Keep at least one non-dot
                        //path segment at the front so it can be mapped
                        //correctly to disk. Otherwise, there is likely
                        //no path mapping for a path starting with '..'.
                        //This can still fail, but catches the most reasonable
                        //uses of ..
                        break;
                    } else if (i > 0) {
                        ary.splice(i - 1, 2);
                        i -= 2;
                    }
                }
            }
        }

        /**
         * Given a relative module name, like ./something, normalize it to
         * a real name that can be mapped to a path.
         * @param {String} name the relative name
         * @param {String} baseName a real name that the name arg is relative
         * to.
         * @param {Boolean} applyMap apply the map config to the value. Should
         * only be done if this normalization is for a dependency ID.
         * @returns {String} normalized name
         */
        function normalize(name, baseName, applyMap) {
            var pkgMain, mapValue, nameParts, i, j, nameSegment, lastIndex,
                foundMap, foundI, foundStarMap, starI,
                baseParts = baseName && baseName.split('/'),
                normalizedBaseParts = baseParts,
                map = config.map,
                starMap = map && map['*'];

            //Adjust any relative paths.
            if (name && name.charAt(0) === '.') {
                //If have a base name, try to normalize against it,
                //otherwise, assume it is a top-level require that will
                //be relative to baseUrl in the end.
                if (baseName) {
                    //Convert baseName to array, and lop off the last part,
                    //so that . matches that 'directory' and not name of the baseName's
                    //module. For instance, baseName of 'one/two/three', maps to
                    //'one/two/three.js', but we want the directory, 'one/two' for
                    //this normalization.
                    normalizedBaseParts = baseParts.slice(0, baseParts.length - 1);
                    name = name.split('/');
                    lastIndex = name.length - 1;

                    // If wanting node ID compatibility, strip .js from end
                    // of IDs. Have to do this here, and not in nameToUrl
                    // because node allows either .js or non .js to map
                    // to same file.
                    if (config.nodeIdCompat && jsSuffixRegExp.test(name[lastIndex])) {
                        name[lastIndex] = name[lastIndex].replace(jsSuffixRegExp, '');
                    }

                    name = normalizedBaseParts.concat(name);
                    trimDots(name);
                    name = name.join('/');
                } else if (name.indexOf('./') === 0) {
                    // No baseName, so this is ID is resolved relative
                    // to baseUrl, pull off the leading dot.
                    name = name.substring(2);
                }
            }

            //Apply map config if available.
            if (applyMap && map && (baseParts || starMap)) {
                nameParts = name.split('/');

                outerLoop: for (i = nameParts.length; i > 0; i -= 1) {
                    nameSegment = nameParts.slice(0, i).join('/');

                    if (baseParts) {
                        //Find the longest baseName segment match in the config.
                        //So, do joins on the biggest to smallest lengths of baseParts.
                        for (j = baseParts.length; j > 0; j -= 1) {
                            mapValue = getOwn(map, baseParts.slice(0, j).join('/'));

                            //baseName segment has config, find if it has one for
                            //this name.
                            if (mapValue) {
                                mapValue = getOwn(mapValue, nameSegment);
                                if (mapValue) {
                                    //Match, update name to the new value.
                                    foundMap = mapValue;
                                    foundI = i;
                                    break outerLoop;
                                }
                            }
                        }
                    }

                    //Check for a star map match, but just hold on to it,
                    //if there is a shorter segment match later in a matching
                    //config, then favor over this star map.
                    if (!foundStarMap && starMap && getOwn(starMap, nameSegment)) {
                        foundStarMap = getOwn(starMap, nameSegment);
                        starI = i;
                    }
                }

                if (!foundMap && foundStarMap) {
                    foundMap = foundStarMap;
                    foundI = starI;
                }

                if (foundMap) {
                    nameParts.splice(0, foundI, foundMap);
                    name = nameParts.join('/');
                }
            }

            // If the name points to a package's name, use
            // the package main instead.
            pkgMain = getOwn(config.pkgs, name);

            return pkgMain ? pkgMain : name;
        }

        function removeScript(name) {
            if (isBrowser) {
                each(scripts(), function (scriptNode) {
                    if (scriptNode.getAttribute('data-requiremodule') === name &&
                            scriptNode.getAttribute('data-requirecontext') === context.contextName) {
                        scriptNode.parentNode.removeChild(scriptNode);
                        return true;
                    }
                });
            }
        }

        function hasPathFallback(id) {
            var pathConfig = getOwn(config.paths, id);
            if (pathConfig && isArray(pathConfig) && pathConfig.length > 1) {
                //Pop off the first array value, since it failed, and
                //retry
                pathConfig.shift();
                context.require.undef(id);
                context.require([id]);
                return true;
            }
        }

        //Turns a plugin!resource to [plugin, resource]
        //with the plugin being undefined if the name
        //did not have a plugin prefix.
        function splitPrefix(name) {
            var prefix,
                index = name ? name.indexOf('!') : -1;
            if (index > -1) {
                prefix = name.substring(0, index);
                name = name.substring(index + 1, name.length);
            }
            return [prefix, name];
        }

        /**
         * Creates a module mapping that includes plugin prefix, module
         * name, and path. If parentModuleMap is provided it will
         * also normalize the name via require.normalize()
         *
         * @param {String} name the module name
         * @param {String} [parentModuleMap] parent module map
         * for the module name, used to resolve relative names.
         * @param {Boolean} isNormalized: is the ID already normalized.
         * This is true if this call is done for a define() module ID.
         * @param {Boolean} applyMap: apply the map config to the ID.
         * Should only be true if this map is for a dependency.
         *
         * @returns {Object}
         */
        function makeModuleMap(name, parentModuleMap, isNormalized, applyMap) {
            var url, pluginModule, suffix, nameParts,
                prefix = null,
                parentName = parentModuleMap ? parentModuleMap.name : null,
                originalName = name,
                isDefine = true,
                normalizedName = '';

            //If no name, then it means it is a require call, generate an
            //internal name.
            if (!name) {
                isDefine = false;
                name = '_@r' + (requireCounter += 1);
            }

            nameParts = splitPrefix(name);
            prefix = nameParts[0];
            name = nameParts[1];

            if (prefix) {
                prefix = normalize(prefix, parentName, applyMap);
                pluginModule = getOwn(defined, prefix);
            }

            //Account for relative paths if there is a base name.
            if (name) {
                if (prefix) {
                    if (pluginModule && pluginModule.normalize) {
                        //Plugin is loaded, use its normalize method.
                        normalizedName = pluginModule.normalize(name, function (name) {
                            return normalize(name, parentName, applyMap);
                        });
                    } else {
                        normalizedName = normalize(name, parentName, applyMap);
                    }
                } else {
                    //A regular module.
                    normalizedName = normalize(name, parentName, applyMap);

                    //Normalized name may be a plugin ID due to map config
                    //application in normalize. The map config values must
                    //already be normalized, so do not need to redo that part.
                    nameParts = splitPrefix(normalizedName);
                    prefix = nameParts[0];
                    normalizedName = nameParts[1];
                    isNormalized = true;

                    url = context.nameToUrl(normalizedName);
                }
            }

            //If the id is a plugin id that cannot be determined if it needs
            //normalization, stamp it with a unique ID so two matching relative
            //ids that may conflict can be separate.
            suffix = prefix && !pluginModule && !isNormalized ?
                     '_unnormalized' + (unnormalizedCounter += 1) :
                     '';

            return {
                prefix: prefix,
                name: normalizedName,
                parentMap: parentModuleMap,
                unnormalized: !!suffix,
                url: url,
                originalName: originalName,
                isDefine: isDefine,
                id: (prefix ?
                        prefix + '!' + normalizedName :
                        normalizedName) + suffix
            };
        }

        function getModule(depMap) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (!mod) {
                mod = registry[id] = new context.Module(depMap);
            }

            return mod;
        }

        function on(depMap, name, fn) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (hasProp(defined, id) &&
                    (!mod || mod.defineEmitComplete)) {
                if (name === 'defined') {
                    fn(defined[id]);
                }
            } else {
                mod = getModule(depMap);
                if (mod.error && name === 'error') {
                    fn(mod.error);
                } else {
                    mod.on(name, fn);
                }
            }
        }

        function onError(err, errback) {
            var ids = err.requireModules,
                notified = false;

            if (errback) {
                errback(err);
            } else {
                each(ids, function (id) {
                    var mod = getOwn(registry, id);
                    if (mod) {
                        //Set error on module, so it skips timeout checks.
                        mod.error = err;
                        if (mod.events.error) {
                            notified = true;
                            mod.emit('error', err);
                        }
                    }
                });

                if (!notified) {
                    req.onError(err);
                }
            }
        }

        /**
         * Internal method to transfer globalQueue items to this context's
         * defQueue.
         */
        function takeGlobalQueue() {
            //Push all the globalDefQueue items into the context's defQueue
            if (globalDefQueue.length) {
                //Array splice in the values since the context code has a
                //local var ref to defQueue, so cannot just reassign the one
                //on context.
                apsp.apply(defQueue,
                           [defQueue.length, 0].concat(globalDefQueue));
                globalDefQueue = [];
            }
        }

        handlers = {
            'require': function (mod) {
                if (mod.require) {
                    return mod.require;
                } else {
                    return (mod.require = context.makeRequire(mod.map));
                }
            },
            'exports': function (mod) {
                mod.usingExports = true;
                if (mod.map.isDefine) {
                    if (mod.exports) {
                        return (defined[mod.map.id] = mod.exports);
                    } else {
                        return (mod.exports = defined[mod.map.id] = {});
                    }
                }
            },
            'module': function (mod) {
                if (mod.module) {
                    return mod.module;
                } else {
                    return (mod.module = {
                        id: mod.map.id,
                        uri: mod.map.url,
                        config: function () {
                            return  getOwn(config.config, mod.map.id) || {};
                        },
                        exports: mod.exports || (mod.exports = {})
                    });
                }
            }
        };

        function cleanRegistry(id) {
            //Clean up machinery used for waiting modules.
            delete registry[id];
            delete enabledRegistry[id];
        }

        function breakCycle(mod, traced, processed) {
            var id = mod.map.id;

            if (mod.error) {
                mod.emit('error', mod.error);
            } else {
                traced[id] = true;
                each(mod.depMaps, function (depMap, i) {
                    var depId = depMap.id,
                        dep = getOwn(registry, depId);

                    //Only force things that have not completed
                    //being defined, so still in the registry,
                    //and only if it has not been matched up
                    //in the module already.
                    if (dep && !mod.depMatched[i] && !processed[depId]) {
                        if (getOwn(traced, depId)) {
                            mod.defineDep(i, defined[depId]);
                            mod.check(); //pass false?
                        } else {
                            breakCycle(dep, traced, processed);
                        }
                    }
                });
                processed[id] = true;
            }
        }

        function checkLoaded() {
            var err, usingPathFallback,
                waitInterval = config.waitSeconds * 1000,
                //It is possible to disable the wait interval by using waitSeconds of 0.
                expired = waitInterval && (context.startTime + waitInterval) < new Date().getTime(),
                noLoads = [],
                reqCalls = [],
                stillLoading = false,
                needCycleCheck = true;

            //Do not bother if this call was a result of a cycle break.
            if (inCheckLoaded) {
                return;
            }

            inCheckLoaded = true;

            //Figure out the state of all the modules.
            eachProp(enabledRegistry, function (mod) {
                var map = mod.map,
                    modId = map.id;

                //Skip things that are not enabled or in error state.
                if (!mod.enabled) {
                    return;
                }

                if (!map.isDefine) {
                    reqCalls.push(mod);
                }

                if (!mod.error) {
                    //If the module should be executed, and it has not
                    //been inited and time is up, remember it.
                    if (!mod.inited && expired) {
                        if (hasPathFallback(modId)) {
                            usingPathFallback = true;
                            stillLoading = true;
                        } else {
                            noLoads.push(modId);
                            removeScript(modId);
                        }
                    } else if (!mod.inited && mod.fetched && map.isDefine) {
                        stillLoading = true;
                        if (!map.prefix) {
                            //No reason to keep looking for unfinished
                            //loading. If the only stillLoading is a
                            //plugin resource though, keep going,
                            //because it may be that a plugin resource
                            //is waiting on a non-plugin cycle.
                            return (needCycleCheck = false);
                        }
                    }
                }
            });

            if (expired && noLoads.length) {
                //If wait time expired, throw error of unloaded modules.
                err = makeError('timeout', 'Load timeout for modules: ' + noLoads, null, noLoads);
                err.contextName = context.contextName;
                return onError(err);
            }

            //Not expired, check for a cycle.
            if (needCycleCheck) {
                each(reqCalls, function (mod) {
                    breakCycle(mod, {}, {});
                });
            }

            //If still waiting on loads, and the waiting load is something
            //other than a plugin resource, or there are still outstanding
            //scripts, then just try back later.
            if ((!expired || usingPathFallback) && stillLoading) {
                //Something is still waiting to load. Wait for it, but only
                //if a timeout is not already in effect.
                if ((isBrowser || isWebWorker) && !checkLoadedTimeoutId) {
                    checkLoadedTimeoutId = setTimeout(function () {
                        checkLoadedTimeoutId = 0;
                        checkLoaded();
                    }, 50);
                }
            }

            inCheckLoaded = false;
        }

        Module = function (map) {
            this.events = getOwn(undefEvents, map.id) || {};
            this.map = map;
            this.shim = getOwn(config.shim, map.id);
            this.depExports = [];
            this.depMaps = [];
            this.depMatched = [];
            this.pluginMaps = {};
            this.depCount = 0;

            /* this.exports this.factory
               this.depMaps = [],
               this.enabled, this.fetched
            */
        };

        Module.prototype = {
            init: function (depMaps, factory, errback, options) {
                options = options || {};

                //Do not do more inits if already done. Can happen if there
                //are multiple define calls for the same module. That is not
                //a normal, common case, but it is also not unexpected.
                if (this.inited) {
                    return;
                }

                this.factory = factory;

                if (errback) {
                    //Register for errors on this module.
                    this.on('error', errback);
                } else if (this.events.error) {
                    //If no errback already, but there are error listeners
                    //on this module, set up an errback to pass to the deps.
                    errback = bind(this, function (err) {
                        this.emit('error', err);
                    });
                }

                //Do a copy of the dependency array, so that
                //source inputs are not modified. For example
                //"shim" deps are passed in here directly, and
                //doing a direct modification of the depMaps array
                //would affect that config.
                this.depMaps = depMaps && depMaps.slice(0);

                this.errback = errback;

                //Indicate this module has be initialized
                this.inited = true;

                this.ignore = options.ignore;

                //Could have option to init this module in enabled mode,
                //or could have been previously marked as enabled. However,
                //the dependencies are not known until init is called. So
                //if enabled previously, now trigger dependencies as enabled.
                if (options.enabled || this.enabled) {
                    //Enable this module and dependencies.
                    //Will call this.check()
                    this.enable();
                } else {
                    this.check();
                }
            },

            defineDep: function (i, depExports) {
                //Because of cycles, defined callback for a given
                //export can be called more than once.
                if (!this.depMatched[i]) {
                    this.depMatched[i] = true;
                    this.depCount -= 1;
                    this.depExports[i] = depExports;
                }
            },

            fetch: function () {
                if (this.fetched) {
                    return;
                }
                this.fetched = true;

                context.startTime = (new Date()).getTime();

                var map = this.map;

                //If the manager is for a plugin managed resource,
                //ask the plugin to load it now.
                if (this.shim) {
                    context.makeRequire(this.map, {
                        enableBuildCallback: true
                    })(this.shim.deps || [], bind(this, function () {
                        return map.prefix ? this.callPlugin() : this.load();
                    }));
                } else {
                    //Regular dependency.
                    return map.prefix ? this.callPlugin() : this.load();
                }
            },

            load: function () {
                var url = this.map.url;

                //Regular dependency.
                if (!urlFetched[url]) {
                    urlFetched[url] = true;
                    context.load(this.map.id, url);
                }
            },

            /**
             * Checks if the module is ready to define itself, and if so,
             * define it.
             */
            check: function () {
                if (!this.enabled || this.enabling) {
                    return;
                }

                var err, cjsModule,
                    id = this.map.id,
                    depExports = this.depExports,
                    exports = this.exports,
                    factory = this.factory;

                if (!this.inited) {
                    this.fetch();
                } else if (this.error) {
                    this.emit('error', this.error);
                } else if (!this.defining) {
                    //The factory could trigger another require call
                    //that would result in checking this module to
                    //define itself again. If already in the process
                    //of doing that, skip this work.
                    this.defining = true;

                    if (this.depCount < 1 && !this.defined) {
                        if (isFunction(factory)) {
                            //If there is an error listener, favor passing
                            //to that instead of throwing an error. However,
                            //only do it for define()'d  modules. require
                            //errbacks should not be called for failures in
                            //their callbacks (#699). However if a global
                            //onError is set, use that.
                            if ((this.events.error && this.map.isDefine) ||
                                req.onError !== defaultOnError) {
                                try {
                                    exports = context.execCb(id, factory, depExports, exports);
                                } catch (e) {
                                    err = e;
                                }
                            } else {
                                exports = context.execCb(id, factory, depExports, exports);
                            }

                            // Favor return value over exports. If node/cjs in play,
                            // then will not have a return value anyway. Favor
                            // module.exports assignment over exports object.
                            if (this.map.isDefine && exports === undefined) {
                                cjsModule = this.module;
                                if (cjsModule) {
                                    exports = cjsModule.exports;
                                } else if (this.usingExports) {
                                    //exports already set the defined value.
                                    exports = this.exports;
                                }
                            }

                            if (err) {
                                err.requireMap = this.map;
                                err.requireModules = this.map.isDefine ? [this.map.id] : null;
                                err.requireType = this.map.isDefine ? 'define' : 'require';
                                return onError((this.error = err));
                            }

                        } else {
                            //Just a literal value
                            exports = factory;
                        }

                        this.exports = exports;

                        if (this.map.isDefine && !this.ignore) {
                            defined[id] = exports;

                            if (req.onResourceLoad) {
                                req.onResourceLoad(context, this.map, this.depMaps);
                            }
                        }

                        //Clean up
                        cleanRegistry(id);

                        this.defined = true;
                    }

                    //Finished the define stage. Allow calling check again
                    //to allow define notifications below in the case of a
                    //cycle.
                    this.defining = false;

                    if (this.defined && !this.defineEmitted) {
                        this.defineEmitted = true;
                        this.emit('defined', this.exports);
                        this.defineEmitComplete = true;
                    }

                }
            },

            callPlugin: function () {
                var map = this.map,
                    id = map.id,
                    //Map already normalized the prefix.
                    pluginMap = makeModuleMap(map.prefix);

                //Mark this as a dependency for this plugin, so it
                //can be traced for cycles.
                this.depMaps.push(pluginMap);

                on(pluginMap, 'defined', bind(this, function (plugin) {
                    var load, normalizedMap, normalizedMod,
                        bundleId = getOwn(bundlesMap, this.map.id),
                        name = this.map.name,
                        parentName = this.map.parentMap ? this.map.parentMap.name : null,
                        localRequire = context.makeRequire(map.parentMap, {
                            enableBuildCallback: true
                        });

                    //If current map is not normalized, wait for that
                    //normalized name to load instead of continuing.
                    if (this.map.unnormalized) {
                        //Normalize the ID if the plugin allows it.
                        if (plugin.normalize) {
                            name = plugin.normalize(name, function (name) {
                                return normalize(name, parentName, true);
                            }) || '';
                        }

                        //prefix and name should already be normalized, no need
                        //for applying map config again either.
                        normalizedMap = makeModuleMap(map.prefix + '!' + name,
                                                      this.map.parentMap);
                        on(normalizedMap,
                            'defined', bind(this, function (value) {
                                this.init([], function () { return value; }, null, {
                                    enabled: true,
                                    ignore: true
                                });
                            }));

                        normalizedMod = getOwn(registry, normalizedMap.id);
                        if (normalizedMod) {
                            //Mark this as a dependency for this plugin, so it
                            //can be traced for cycles.
                            this.depMaps.push(normalizedMap);

                            if (this.events.error) {
                                normalizedMod.on('error', bind(this, function (err) {
                                    this.emit('error', err);
                                }));
                            }
                            normalizedMod.enable();
                        }

                        return;
                    }

                    //If a paths config, then just load that file instead to
                    //resolve the plugin, as it is built into that paths layer.
                    if (bundleId) {
                        this.map.url = context.nameToUrl(bundleId);
                        this.load();
                        return;
                    }

                    load = bind(this, function (value) {
                        this.init([], function () { return value; }, null, {
                            enabled: true
                        });
                    });

                    load.error = bind(this, function (err) {
                        this.inited = true;
                        this.error = err;
                        err.requireModules = [id];

                        //Remove temp unnormalized modules for this module,
                        //since they will never be resolved otherwise now.
                        eachProp(registry, function (mod) {
                            if (mod.map.id.indexOf(id + '_unnormalized') === 0) {
                                cleanRegistry(mod.map.id);
                            }
                        });

                        onError(err);
                    });

                    //Allow plugins to load other code without having to know the
                    //context or how to 'complete' the load.
                    load.fromText = bind(this, function (text, textAlt) {
                        /*jslint evil: true */
                        var moduleName = map.name,
                            moduleMap = makeModuleMap(moduleName),
                            hasInteractive = useInteractive;

                        //As of 2.1.0, support just passing the text, to reinforce
                        //fromText only being called once per resource. Still
                        //support old style of passing moduleName but discard
                        //that moduleName in favor of the internal ref.
                        if (textAlt) {
                            text = textAlt;
                        }

                        //Turn off interactive script matching for IE for any define
                        //calls in the text, then turn it back on at the end.
                        if (hasInteractive) {
                            useInteractive = false;
                        }

                        //Prime the system by creating a module instance for
                        //it.
                        getModule(moduleMap);

                        //Transfer any config to this other module.
                        if (hasProp(config.config, id)) {
                            config.config[moduleName] = config.config[id];
                        }

                        try {
                            req.exec(text);
                        } catch (e) {
                            return onError(makeError('fromtexteval',
                                             'fromText eval for ' + id +
                                            ' failed: ' + e,
                                             e,
                                             [id]));
                        }

                        if (hasInteractive) {
                            useInteractive = true;
                        }

                        //Mark this as a dependency for the plugin
                        //resource
                        this.depMaps.push(moduleMap);

                        //Support anonymous modules.
                        context.completeLoad(moduleName);

                        //Bind the value of that module to the value for this
                        //resource ID.
                        localRequire([moduleName], load);
                    });

                    //Use parentName here since the plugin's name is not reliable,
                    //could be some weird string with no path that actually wants to
                    //reference the parentName's path.
                    plugin.load(map.name, localRequire, load, config);
                }));

                context.enable(pluginMap, this);
                this.pluginMaps[pluginMap.id] = pluginMap;
            },

            enable: function () {
                enabledRegistry[this.map.id] = this;
                this.enabled = true;

                //Set flag mentioning that the module is enabling,
                //so that immediate calls to the defined callbacks
                //for dependencies do not trigger inadvertent load
                //with the depCount still being zero.
                this.enabling = true;

                //Enable each dependency
                each(this.depMaps, bind(this, function (depMap, i) {
                    var id, mod, handler;

                    if (typeof depMap === 'string') {
                        //Dependency needs to be converted to a depMap
                        //and wired up to this module.
                        depMap = makeModuleMap(depMap,
                                               (this.map.isDefine ? this.map : this.map.parentMap),
                                               false,
                                               !this.skipMap);
                        this.depMaps[i] = depMap;

                        handler = getOwn(handlers, depMap.id);

                        if (handler) {
                            this.depExports[i] = handler(this);
                            return;
                        }

                        this.depCount += 1;

                        on(depMap, 'defined', bind(this, function (depExports) {
                            this.defineDep(i, depExports);
                            this.check();
                        }));

                        if (this.errback) {
                            on(depMap, 'error', bind(this, this.errback));
                        }
                    }

                    id = depMap.id;
                    mod = registry[id];

                    //Skip special modules like 'require', 'exports', 'module'
                    //Also, don't call enable if it is already enabled,
                    //important in circular dependency cases.
                    if (!hasProp(handlers, id) && mod && !mod.enabled) {
                        context.enable(depMap, this);
                    }
                }));

                //Enable each plugin that is used in
                //a dependency
                eachProp(this.pluginMaps, bind(this, function (pluginMap) {
                    var mod = getOwn(registry, pluginMap.id);
                    if (mod && !mod.enabled) {
                        context.enable(pluginMap, this);
                    }
                }));

                this.enabling = false;

                this.check();
            },

            on: function (name, cb) {
                var cbs = this.events[name];
                if (!cbs) {
                    cbs = this.events[name] = [];
                }
                cbs.push(cb);
            },

            emit: function (name, evt) {
                each(this.events[name], function (cb) {
                    cb(evt);
                });
                if (name === 'error') {
                    //Now that the error handler was triggered, remove
                    //the listeners, since this broken Module instance
                    //can stay around for a while in the registry.
                    delete this.events[name];
                }
            }
        };

        function callGetModule(args) {
            //Skip modules already defined.
            if (!hasProp(defined, args[0])) {
                getModule(makeModuleMap(args[0], null, true)).init(args[1], args[2]);
            }
        }

        function removeListener(node, func, name, ieName) {
            //Favor detachEvent because of IE9
            //issue, see attachEvent/addEventListener comment elsewhere
            //in this file.
            if (node.detachEvent && !isOpera) {
                //Probably IE. If not it will throw an error, which will be
                //useful to know.
                if (ieName) {
                    node.detachEvent(ieName, func);
                }
            } else {
                node.removeEventListener(name, func, false);
            }
        }

        /**
         * Given an event from a script node, get the requirejs info from it,
         * and then removes the event listeners on the node.
         * @param {Event} evt
         * @returns {Object}
         */
        function getScriptData(evt) {
            //Using currentTarget instead of target for Firefox 2.0's sake. Not
            //all old browsers will be supported, but this one was easy enough
            //to support and still makes sense.
            var node = evt.currentTarget || evt.srcElement;

            //Remove the listeners once here.
            removeListener(node, context.onScriptLoad, 'load', 'onreadystatechange');
            removeListener(node, context.onScriptError, 'error');

            return {
                node: node,
                id: node && node.getAttribute('data-requiremodule')
            };
        }

        function intakeDefines() {
            var args;

            //Any defined modules in the global queue, intake them now.
            takeGlobalQueue();

            //Make sure any remaining defQueue items get properly processed.
            while (defQueue.length) {
                args = defQueue.shift();
                if (args[0] === null) {
                    return onError(makeError('mismatch', 'Mismatched anonymous define() module: ' + args[args.length - 1]));
                } else {
                    //args are id, deps, factory. Should be normalized by the
                    //define() function.
                    callGetModule(args);
                }
            }
        }

        context = {
            config: config,
            contextName: contextName,
            registry: registry,
            defined: defined,
            urlFetched: urlFetched,
            defQueue: defQueue,
            Module: Module,
            makeModuleMap: makeModuleMap,
            nextTick: req.nextTick,
            onError: onError,

            /**
             * Set a configuration for the context.
             * @param {Object} cfg config object to integrate.
             */
            configure: function (cfg) {
                //Make sure the baseUrl ends in a slash.
                if (cfg.baseUrl) {
                    if (cfg.baseUrl.charAt(cfg.baseUrl.length - 1) !== '/') {
                        cfg.baseUrl += '/';
                    }
                }

                //Save off the paths since they require special processing,
                //they are additive.
                var shim = config.shim,
                    objs = {
                        paths: true,
                        bundles: true,
                        config: true,
                        map: true
                    };

                eachProp(cfg, function (value, prop) {
                    if (objs[prop]) {
                        if (!config[prop]) {
                            config[prop] = {};
                        }
                        mixin(config[prop], value, true, true);
                    } else {
                        config[prop] = value;
                    }
                });

                //Reverse map the bundles
                if (cfg.bundles) {
                    eachProp(cfg.bundles, function (value, prop) {
                        each(value, function (v) {
                            if (v !== prop) {
                                bundlesMap[v] = prop;
                            }
                        });
                    });
                }

                //Merge shim
                if (cfg.shim) {
                    eachProp(cfg.shim, function (value, id) {
                        //Normalize the structure
                        if (isArray(value)) {
                            value = {
                                deps: value
                            };
                        }
                        if ((value.exports || value.init) && !value.exportsFn) {
                            value.exportsFn = context.makeShimExports(value);
                        }
                        shim[id] = value;
                    });
                    config.shim = shim;
                }

                //Adjust packages if necessary.
                if (cfg.packages) {
                    each(cfg.packages, function (pkgObj) {
                        var location, name;

                        pkgObj = typeof pkgObj === 'string' ? { name: pkgObj } : pkgObj;

                        name = pkgObj.name;
                        location = pkgObj.location;
                        if (location) {
                            config.paths[name] = pkgObj.location;
                        }

                        //Save pointer to main module ID for pkg name.
                        //Remove leading dot in main, so main paths are normalized,
                        //and remove any trailing .js, since different package
                        //envs have different conventions: some use a module name,
                        //some use a file name.
                        config.pkgs[name] = pkgObj.name + '/' + (pkgObj.main || 'main')
                                     .replace(currDirRegExp, '')
                                     .replace(jsSuffixRegExp, '');
                    });
                }

                //If there are any "waiting to execute" modules in the registry,
                //update the maps for them, since their info, like URLs to load,
                //may have changed.
                eachProp(registry, function (mod, id) {
                    //If module already has init called, since it is too
                    //late to modify them, and ignore unnormalized ones
                    //since they are transient.
                    if (!mod.inited && !mod.map.unnormalized) {
                        mod.map = makeModuleMap(id);
                    }
                });

                //If a deps array or a config callback is specified, then call
                //require with those args. This is useful when require is defined as a
                //config object before require.js is loaded.
                if (cfg.deps || cfg.callback) {
                    context.require(cfg.deps || [], cfg.callback);
                }
            },

            makeShimExports: function (value) {
                function fn() {
                    var ret;
                    if (value.init) {
                        ret = value.init.apply(global, arguments);
                    }
                    return ret || (value.exports && getGlobal(value.exports));
                }
                return fn;
            },

            makeRequire: function (relMap, options) {
                options = options || {};

                function localRequire(deps, callback, errback) {
                    var id, map, requireMod;

                    if (options.enableBuildCallback && callback && isFunction(callback)) {
                        callback.__requireJsBuild = true;
                    }

                    if (typeof deps === 'string') {
                        if (isFunction(callback)) {
                            //Invalid call
                            return onError(makeError('requireargs', 'Invalid require call'), errback);
                        }

                        //If require|exports|module are requested, get the
                        //value for them from the special handlers. Caveat:
                        //this only works while module is being defined.
                        if (relMap && hasProp(handlers, deps)) {
                            return handlers[deps](registry[relMap.id]);
                        }

                        //Synchronous access to one module. If require.get is
                        //available (as in the Node adapter), prefer that.
                        if (req.get) {
                            return req.get(context, deps, relMap, localRequire);
                        }

                        //Normalize module name, if it contains . or ..
                        map = makeModuleMap(deps, relMap, false, true);
                        id = map.id;

                        if (!hasProp(defined, id)) {
                            return onError(makeError('notloaded', 'Module name "' +
                                        id +
                                        '" has not been loaded yet for context: ' +
                                        contextName +
                                        (relMap ? '' : '. Use require([])')));
                        }
                        return defined[id];
                    }

                    //Grab defines waiting in the global queue.
                    intakeDefines();

                    //Mark all the dependencies as needing to be loaded.
                    context.nextTick(function () {
                        //Some defines could have been added since the
                        //require call, collect them.
                        intakeDefines();

                        requireMod = getModule(makeModuleMap(null, relMap));

                        //Store if map config should be applied to this require
                        //call for dependencies.
                        requireMod.skipMap = options.skipMap;

                        requireMod.init(deps, callback, errback, {
                            enabled: true
                        });

                        checkLoaded();
                    });

                    return localRequire;
                }

                mixin(localRequire, {
                    isBrowser: isBrowser,

                    /**
                     * Converts a module name + .extension into an URL path.
                     * *Requires* the use of a module name. It does not support using
                     * plain URLs like nameToUrl.
                     */
                    toUrl: function (moduleNamePlusExt) {
                        var ext,
                            index = moduleNamePlusExt.lastIndexOf('.'),
                            segment = moduleNamePlusExt.split('/')[0],
                            isRelative = segment === '.' || segment === '..';

                        //Have a file extension alias, and it is not the
                        //dots from a relative path.
                        if (index !== -1 && (!isRelative || index > 1)) {
                            ext = moduleNamePlusExt.substring(index, moduleNamePlusExt.length);
                            moduleNamePlusExt = moduleNamePlusExt.substring(0, index);
                        }

                        return context.nameToUrl(normalize(moduleNamePlusExt,
                                                relMap && relMap.id, true), ext,  true);
                    },

                    defined: function (id) {
                        return hasProp(defined, makeModuleMap(id, relMap, false, true).id);
                    },

                    specified: function (id) {
                        id = makeModuleMap(id, relMap, false, true).id;
                        return hasProp(defined, id) || hasProp(registry, id);
                    }
                });

                //Only allow undef on top level require calls
                if (!relMap) {
                    localRequire.undef = function (id) {
                        //Bind any waiting define() calls to this context,
                        //fix for #408
                        takeGlobalQueue();

                        var map = makeModuleMap(id, relMap, true),
                            mod = getOwn(registry, id);

                        removeScript(id);

                        delete defined[id];
                        delete urlFetched[map.url];
                        delete undefEvents[id];

                        //Clean queued defines too. Go backwards
                        //in array so that the splices do not
                        //mess up the iteration.
                        eachReverse(defQueue, function(args, i) {
                            if(args[0] === id) {
                                defQueue.splice(i, 1);
                            }
                        });

                        if (mod) {
                            //Hold on to listeners in case the
                            //module will be attempted to be reloaded
                            //using a different config.
                            if (mod.events.defined) {
                                undefEvents[id] = mod.events;
                            }

                            cleanRegistry(id);
                        }
                    };
                }

                return localRequire;
            },

            /**
             * Called to enable a module if it is still in the registry
             * awaiting enablement. A second arg, parent, the parent module,
             * is passed in for context, when this method is overridden by
             * the optimizer. Not shown here to keep code compact.
             */
            enable: function (depMap) {
                var mod = getOwn(registry, depMap.id);
                if (mod) {
                    getModule(depMap).enable();
                }
            },

            /**
             * Internal method used by environment adapters to complete a load event.
             * A load event could be a script load or just a load pass from a synchronous
             * load call.
             * @param {String} moduleName the name of the module to potentially complete.
             */
            completeLoad: function (moduleName) {
                var found, args, mod,
                    shim = getOwn(config.shim, moduleName) || {},
                    shExports = shim.exports;

                takeGlobalQueue();

                while (defQueue.length) {
                    args = defQueue.shift();
                    if (args[0] === null) {
                        args[0] = moduleName;
                        //If already found an anonymous module and bound it
                        //to this name, then this is some other anon module
                        //waiting for its completeLoad to fire.
                        if (found) {
                            break;
                        }
                        found = true;
                    } else if (args[0] === moduleName) {
                        //Found matching define call for this script!
                        found = true;
                    }

                    callGetModule(args);
                }

                //Do this after the cycle of callGetModule in case the result
                //of those calls/init calls changes the registry.
                mod = getOwn(registry, moduleName);

                if (!found && !hasProp(defined, moduleName) && mod && !mod.inited) {
                    if (config.enforceDefine && (!shExports || !getGlobal(shExports))) {
                        if (hasPathFallback(moduleName)) {
                            return;
                        } else {
                            return onError(makeError('nodefine',
                                             'No define call for ' + moduleName,
                                             null,
                                             [moduleName]));
                        }
                    } else {
                        //A script that does not call define(), so just simulate
                        //the call for it.
                        callGetModule([moduleName, (shim.deps || []), shim.exportsFn]);
                    }
                }

                checkLoaded();
            },

            /**
             * Converts a module name to a file path. Supports cases where
             * moduleName may actually be just an URL.
             * Note that it **does not** call normalize on the moduleName,
             * it is assumed to have already been normalized. This is an
             * internal API, not a public one. Use toUrl for the public API.
             */
            nameToUrl: function (moduleName, ext, skipExt) {
                var paths, syms, i, parentModule, url,
                    parentPath, bundleId,
                    pkgMain = getOwn(config.pkgs, moduleName);

                if (pkgMain) {
                    moduleName = pkgMain;
                }

                bundleId = getOwn(bundlesMap, moduleName);

                if (bundleId) {
                    return context.nameToUrl(bundleId, ext, skipExt);
                }

                //If a colon is in the URL, it indicates a protocol is used and it is just
                //an URL to a file, or if it starts with a slash, contains a query arg (i.e. ?)
                //or ends with .js, then assume the user meant to use an url and not a module id.
                //The slash is important for protocol-less URLs as well as full paths.
                if (req.jsExtRegExp.test(moduleName)) {
                    //Just a plain path, not module name lookup, so just return it.
                    //Add extension if it is included. This is a bit wonky, only non-.js things pass
                    //an extension, this method probably needs to be reworked.
                    url = moduleName + (ext || '');
                } else {
                    //A module that needs to be converted to a path.
                    paths = config.paths;

                    syms = moduleName.split('/');
                    //For each module name segment, see if there is a path
                    //registered for it. Start with most specific name
                    //and work up from it.
                    for (i = syms.length; i > 0; i -= 1) {
                        parentModule = syms.slice(0, i).join('/');

                        parentPath = getOwn(paths, parentModule);
                        if (parentPath) {
                            //If an array, it means there are a few choices,
                            //Choose the one that is desired
                            if (isArray(parentPath)) {
                                parentPath = parentPath[0];
                            }
                            syms.splice(0, i, parentPath);
                            break;
                        }
                    }

                    //Join the path parts together, then figure out if baseUrl is needed.
                    url = syms.join('/');
                    url += (ext || (/^data\:|\?/.test(url) || skipExt ? '' : '.js'));
                    url = (url.charAt(0) === '/' || url.match(/^[\w\+\.\-]+:/) ? '' : config.baseUrl) + url;
                }

                return config.urlArgs ? url +
                                        ((url.indexOf('?') === -1 ? '?' : '&') +
                                         config.urlArgs) : url;
            },

            //Delegates to req.load. Broken out as a separate function to
            //allow overriding in the optimizer.
            load: function (id, url) {
                req.load(context, id, url);
            },

            /**
             * Executes a module callback function. Broken out as a separate function
             * solely to allow the build system to sequence the files in the built
             * layer in the right sequence.
             *
             * @private
             */
            execCb: function (name, callback, args, exports) {
                return callback.apply(exports, args);
            },

            /**
             * callback for script loads, used to check status of loading.
             *
             * @param {Event} evt the event from the browser for the script
             * that was loaded.
             */
            onScriptLoad: function (evt) {
                //Using currentTarget instead of target for Firefox 2.0's sake. Not
                //all old browsers will be supported, but this one was easy enough
                //to support and still makes sense.
                if (evt.type === 'load' ||
                        (readyRegExp.test((evt.currentTarget || evt.srcElement).readyState))) {
                    //Reset interactive script so a script node is not held onto for
                    //to long.
                    interactiveScript = null;

                    //Pull out the name of the module and the context.
                    var data = getScriptData(evt);
                    context.completeLoad(data.id);
                }
            },

            /**
             * Callback for script errors.
             */
            onScriptError: function (evt) {
                var data = getScriptData(evt);
                if (!hasPathFallback(data.id)) {
                    return onError(makeError('scripterror', 'Script error for: ' + data.id, evt, [data.id]));
                }
            }
        };

        context.require = context.makeRequire();
        return context;
    }

    /**
     * Main entry point.
     *
     * If the only argument to require is a string, then the module that
     * is represented by that string is fetched for the appropriate context.
     *
     * If the first argument is an array, then it will be treated as an array
     * of dependency string names to fetch. An optional function callback can
     * be specified to execute when all of those dependencies are available.
     *
     * Make a local req variable to help Caja compliance (it assumes things
     * on a require that are not standardized), and to give a short
     * name for minification/local scope use.
     */
    req = requirejs = function (deps, callback, errback, optional) {

        //Find the right context, use default
        var context, config,
            contextName = defContextName;

        // Determine if have config object in the call.
        if (!isArray(deps) && typeof deps !== 'string') {
            // deps is a config object
            config = deps;
            if (isArray(callback)) {
                // Adjust args if there are dependencies
                deps = callback;
                callback = errback;
                errback = optional;
            } else {
                deps = [];
            }
        }

        if (config && config.context) {
            contextName = config.context;
        }

        context = getOwn(contexts, contextName);
        if (!context) {
            context = contexts[contextName] = req.s.newContext(contextName);
        }

        if (config) {
            context.configure(config);
        }

        return context.require(deps, callback, errback);
    };

    /**
     * Support require.config() to make it easier to cooperate with other
     * AMD loaders on globally agreed names.
     */
    req.config = function (config) {
        return req(config);
    };

    /**
     * Execute something after the current tick
     * of the event loop. Override for other envs
     * that have a better solution than setTimeout.
     * @param  {Function} fn function to execute later.
     */
    req.nextTick = typeof setTimeout !== 'undefined' ? function (fn) {
        setTimeout(fn, 4);
    } : function (fn) { fn(); };

    /**
     * Export require as a global, but only if it does not already exist.
     */
    if (!require) {
        require = req;
    }

    req.version = version;

    //Used to filter out dependencies that are already paths.
    req.jsExtRegExp = /^\/|:|\?|\.js$/;
    req.isBrowser = isBrowser;
    s = req.s = {
        contexts: contexts,
        newContext: newContext
    };

    //Create default context.
    req({});

    //Exports some context-sensitive methods on global require.
    each([
        'toUrl',
        'undef',
        'defined',
        'specified'
    ], function (prop) {
        //Reference from contexts instead of early binding to default context,
        //so that during builds, the latest instance of the default context
        //with its config gets used.
        req[prop] = function () {
            var ctx = contexts[defContextName];
            return ctx.require[prop].apply(ctx, arguments);
        };
    });

    if (isBrowser) {
        head = s.head = document.getElementsByTagName('head')[0];
        //If BASE tag is in play, using appendChild is a problem for IE6.
        //When that browser dies, this can be removed. Details in this jQuery bug:
        //http://dev.jquery.com/ticket/2709
        baseElement = document.getElementsByTagName('base')[0];
        if (baseElement) {
            head = s.head = baseElement.parentNode;
        }
    }

    /**
     * Any errors that require explicitly generates will be passed to this
     * function. Intercept/override it if you want custom error handling.
     * @param {Error} err the error object.
     */
    req.onError = defaultOnError;

    /**
     * Creates the node for the load command. Only used in browser envs.
     */
    req.createNode = function (config, moduleName, url) {
        var node = config.xhtml ?
                document.createElementNS('http://www.w3.org/1999/xhtml', 'html:script') :
                document.createElement('script');
        node.type = config.scriptType || 'text/javascript';
        node.charset = 'utf-8';
        node.async = true;
        return node;
    };

    /**
     * Does the request to load a module for the browser case.
     * Make this a separate function to allow other environments
     * to override it.
     *
     * @param {Object} context the require context to find state.
     * @param {String} moduleName the name of the module.
     * @param {Object} url the URL to the module.
     */
    req.load = function (context, moduleName, url) {
        var config = (context && context.config) || {},
            node;
        if (isBrowser) {
            //In the browser so use a script tag
            node = req.createNode(config, moduleName, url);

            node.setAttribute('data-requirecontext', context.contextName);
            node.setAttribute('data-requiremodule', moduleName);

            //Set up load listener. Test attachEvent first because IE9 has
            //a subtle issue in its addEventListener and script onload firings
            //that do not match the behavior of all other browsers with
            //addEventListener support, which fire the onload event for a
            //script right after the script execution. See:
            //https://connect.microsoft.com/IE/feedback/details/648057/script-onload-event-is-not-fired-immediately-after-script-execution
            //UNFORTUNATELY Opera implements attachEvent but does not follow the script
            //script execution mode.
            if (node.attachEvent &&
                    //Check if node.attachEvent is artificially added by custom script or
                    //natively supported by browser
                    //read https://github.com/jrburke/requirejs/issues/187
                    //if we can NOT find [native code] then it must NOT natively supported.
                    //in IE8, node.attachEvent does not have toString()
                    //Note the test for "[native code" with no closing brace, see:
                    //https://github.com/jrburke/requirejs/issues/273
                    !(node.attachEvent.toString && node.attachEvent.toString().indexOf('[native code') < 0) &&
                    !isOpera) {
                //Probably IE. IE (at least 6-8) do not fire
                //script onload right after executing the script, so
                //we cannot tie the anonymous define call to a name.
                //However, IE reports the script as being in 'interactive'
                //readyState at the time of the define call.
                useInteractive = true;

                node.attachEvent('onreadystatechange', context.onScriptLoad);
                //It would be great to add an error handler here to catch
                //404s in IE9+. However, onreadystatechange will fire before
                //the error handler, so that does not help. If addEventListener
                //is used, then IE will fire error before load, but we cannot
                //use that pathway given the connect.microsoft.com issue
                //mentioned above about not doing the 'script execute,
                //then fire the script load event listener before execute
                //next script' that other browsers do.
                //Best hope: IE10 fixes the issues,
                //and then destroys all installs of IE 6-9.
                //node.attachEvent('onerror', context.onScriptError);
            } else {
                node.addEventListener('load', context.onScriptLoad, false);
                node.addEventListener('error', context.onScriptError, false);
            }
            node.src = url;

            //For some cache cases in IE 6-8, the script executes before the end
            //of the appendChild execution, so to tie an anonymous define
            //call to the module name (which is stored on the node), hold on
            //to a reference to this node, but clear after the DOM insertion.
            currentlyAddingScript = node;
            if (baseElement) {
                head.insertBefore(node, baseElement);
            } else {
                head.appendChild(node);
            }
            currentlyAddingScript = null;

            return node;
        } else if (isWebWorker) {
            try {
                //In a web worker, use importScripts. This is not a very
                //efficient use of importScripts, importScripts will block until
                //its script is downloaded and evaluated. However, if web workers
                //are in play, the expectation that a build has been done so that
                //only one script needs to be loaded anyway. This may need to be
                //reevaluated if other use cases become common.
                importScripts(url);

                //Account for anonymous modules
                context.completeLoad(moduleName);
            } catch (e) {
                context.onError(makeError('importscripts',
                                'importScripts failed for ' +
                                    moduleName + ' at ' + url,
                                e,
                                [moduleName]));
            }
        }
    };

    function getInteractiveScript() {
        if (interactiveScript && interactiveScript.readyState === 'interactive') {
            return interactiveScript;
        }

        eachReverse(scripts(), function (script) {
            if (script.readyState === 'interactive') {
                return (interactiveScript = script);
            }
        });
        return interactiveScript;
    }

    //Look for a data-main script attribute, which could also adjust the baseUrl.
    if (isBrowser && !cfg.skipDataMain) {
        //Figure out baseUrl. Get it from the script tag with require.js in it.
        eachReverse(scripts(), function (script) {
            //Set the 'head' where we can append children by
            //using the script's parent.
            if (!head) {
                head = script.parentNode;
            }

            //Look for a data-main attribute to set main script for the page
            //to load. If it is there, the path to data main becomes the
            //baseUrl, if it is not already set.
            dataMain = script.getAttribute('data-main');
            if (dataMain) {
                //Preserve dataMain in case it is a path (i.e. contains '?')
                mainScript = dataMain;

                //Set final baseUrl if there is not already an explicit one.
                if (!cfg.baseUrl) {
                    //Pull off the directory of data-main for use as the
                    //baseUrl.
                    src = mainScript.split('/');
                    mainScript = src.pop();
                    subPath = src.length ? src.join('/')  + '/' : './';

                    cfg.baseUrl = subPath;
                }

                //Strip off any trailing .js since mainScript is now
                //like a module name.
                mainScript = mainScript.replace(jsSuffixRegExp, '');

                 //If mainScript is still a path, fall back to dataMain
                if (req.jsExtRegExp.test(mainScript)) {
                    mainScript = dataMain;
                }

                //Put the data-main script in the files to load.
                cfg.deps = cfg.deps ? cfg.deps.concat(mainScript) : [mainScript];

                return true;
            }
        });
    }

    /**
     * The function that handles definitions of modules. Differs from
     * require() in that a string for the module should be the first argument,
     * and the function to execute after dependencies are loaded should
     * return a value to define the module corresponding to the first argument's
     * name.
     */
    define = function (name, deps, callback) {
        var node, context;

        //Allow for anonymous modules
        if (typeof name !== 'string') {
            //Adjust args appropriately
            callback = deps;
            deps = name;
            name = null;
        }

        //This module may not have dependencies
        if (!isArray(deps)) {
            callback = deps;
            deps = null;
        }

        //If no name, and callback is a function, then figure out if it a
        //CommonJS thing with dependencies.
        if (!deps && isFunction(callback)) {
            deps = [];
            //Remove comments from the callback string,
            //look for require calls, and pull them into the dependencies,
            //but only if there are function args.
            if (callback.length) {
                callback
                    .toString()
                    .replace(commentRegExp, '')
                    .replace(cjsRequireRegExp, function (match, dep) {
                        deps.push(dep);
                    });

                //May be a CommonJS thing even without require calls, but still
                //could use exports, and module. Avoid doing exports and module
                //work though if it just needs require.
                //REQUIRES the function to expect the CommonJS variables in the
                //order listed below.
                deps = (callback.length === 1 ? ['require'] : ['require', 'exports', 'module']).concat(deps);
            }
        }

        //If in IE 6-8 and hit an anonymous define() call, do the interactive
        //work.
        if (useInteractive) {
            node = currentlyAddingScript || getInteractiveScript();
            if (node) {
                if (!name) {
                    name = node.getAttribute('data-requiremodule');
                }
                context = contexts[node.getAttribute('data-requirecontext')];
            }
        }

        //Always save off evaluating the def call until the script onload handler.
        //This allows multiple modules to be in a file without prematurely
        //tracing dependencies, and allows for anonymous module support,
        //where the module name is not known until the script onload event
        //occurs. If no context, use the global queue, and get it processed
        //in the onscript load callback.
        (context ? context.defQueue : globalDefQueue).push([name, deps, callback]);
    };

    define.amd = {
        jQuery: true
    };


    /**
     * Executes the text. Normally just uses eval, but can be modified
     * to use a better, environment-specific call. Only used for transpiling
     * loader plugins, not for plain JS modules.
     * @param {String} text the text to execute/evaluate.
     */
    req.exec = function (text) {
        /*jslint evil: true */
        return eval(text);
    };

    //Set up with config info.
    req(cfg);
}(this));



/*! jQuery v1.11.0 | (c) 2005, 2014 jQuery Foundation, Inc. | jquery.org/license */

/*! Picturefill - v2.3.0 - 2015-03-23
* http://scottjehl.github.io/picturefill
* Copyright (c) 2015 https://github.com/scottjehl/picturefill/blob/master/Authors.txt; Licensed MIT */

//     Underscore.js 1.6.0
//     http://underscorejs.org
//     (c) 2009-2014 Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
//     Underscore may be freely distributed under the MIT license.

/*! Copyright (c) 2013 Brandon Aaron (http://brandon.aaron.sh)
 * Licensed under the MIT License (LICENSE.txt).
 *
 * Version: 3.1.12
 *
 * Requires: jQuery 1.2.2+
 */

/*! jQuery UI - v1.11.4 - 2015-11-20
* http://jqueryui.com
* Includes: effect.js
* Copyright jQuery Foundation and other contributors; Licensed MIT */

/*! jquery.cookie v1.4.1 | MIT */

// (c) Steven Levithan <stevenlevithan.com>

/*!
 * jQuery Form Plugin
 * version: 3.51.0-2014.06.20
 * Requires jQuery v1.5 or later
 * Copyright (c) 2014 M. Alsup
 * Examples and documentation at: http://malsup.com/jquery/form/
 * Project repository: https://github.com/malsup/form
 * Dual licensed under the MIT and GPL licenses.
 * https://github.com/malsup/form#copyright-and-license
 */

/*! jQuery Validation Plugin - v1.13.1 - 10/14/2014
 * http://jqueryvalidation.org/
 * Copyright (c) 2014 Jörn Zaefferer; Licensed MIT */

!function(e, t) {
    "object" == typeof module && "object" == typeof module.exports ? module.exports = e.document ? t(e, !0) : function(e) {
        if (!e.document)
            throw new Error("jQuery requires a window with a document");
        return t(e)
    } : t(e)
}("undefined" != typeof window ? window : this, function(e, t) {
    function y(e) {
        var t = e.length,
            n = p.type(e);
        return "function" === n || p.isWindow(e) ? !1 : 1 === e.nodeType && t ? !0 : "array" === n || 0 === t || "number" == typeof t && t > 0 && t - 1 in e
    }
    function x(e, t, n) {
        if (p.isFunction(t))
            return p.grep(e, function(e, r) {
                return !!t.call(e, r, e) !== n
            });
        if (t.nodeType)
            return p.grep(e, function(e) {
                return e === t !== n
            });
        if ("string" == typeof t) {
            if (S.test(t))
                return p.filter(t, e, n);
            t = p.filter(t, e)
        }
        return p.grep(e, function(e) {
            return p.inArray(e, t) >= 0 !== n
        })
    }
    function O(e, t) {
        do e = e[t];
        while (e && 1 !== e.nodeType);
        return e
    }
    function D(e) {
        var t = _[e] = {};
        return p.each(e.match(M) || [], function(e, n) {
            t[n] = !0
        }), t
    }
    function H() {
        N.addEventListener ? (N.removeEventListener("DOMContentLoaded", B, !1), e.removeEventListener("load", B, !1)) : (N.detachEvent("onreadystatechange", B), e.detachEvent("onload", B))
    }
    function B() {
        (N.addEventListener || "load" === event.type || "complete" === N.readyState) && (H(), p.ready())
    }
    function R(e, t, n) {
        if (void 0 === n && 1 === e.nodeType) {
            var r = "data-" + t.replace(q, "-$1").toLowerCase();
            if (n = e.getAttribute(r), "string" == typeof n) {
                try {
                    n = "true" === n ? !0 : "false" === n ? !1 : "null" === n ? null : +n + "" === n ? +n : I.test(n) ? p.parseJSON(n) : n
                } catch (i) {}
                p.data(e, t, n)
            } else
                n = void 0
        }
        return n
    }
    function U(e) {
        var t;
        for (t in e)
            if (("data" !== t || !p.isEmptyObject(e[t])) && "toJSON" !== t)
                return !1;
        return !0
    }
    function z(e, t, r, i) {
        if (p.acceptData(e)) {
            var s,
                o,
                u = p.expando,
                a = e.nodeType,
                f = a ? p.cache : e,
                l = a ? e[u] : e[u] && u;
            if (l && f[l] && (i || f[l].data) || void 0 !== r || "string" != typeof t)
                return l || (l = a ? e[u] = n.pop() || p.guid++ : u), f[l] || (f[l] = a ? {} : {
                    toJSON: p.noop
                }), ("object" == typeof t || "function" == typeof t) && (i ? f[l] = p.extend(f[l], t) : f[l].data = p.extend(f[l].data, t)), o = f[l], i || (o.data || (o.data = {}), o = o.data), void 0 !== r && (o[p.camelCase(t)] = r), "string" == typeof t ? (s = o[t], null == s && (s = o[p.camelCase(t)])) : s = o, s
        }
    }
    function W(e, t, n) {
        if (p.acceptData(e)) {
            var r,
                i,
                s = e.nodeType,
                o = s ? p.cache : e,
                u = s ? e[p.expando] : p.expando;
            if (o[u]) {
                if (t && (r = n ? o[u] : o[u].data)) {
                    p.isArray(t) ? t = t.concat(p.map(t, p.camelCase)) : t in r ? t = [t] : (t = p.camelCase(t), t = t in r ? [t] : t.split(" ")), i = t.length;
                    while (i--)
                        delete r[t[i]];
                    if (n ? !U(r) : !p.isEmptyObject(r))
                        return
                }
                (n || (delete o[u].data, U(o[u]))) && (s ? p.cleanData([e], !0) : c.deleteExpando || o != o.window ? delete o[u] : o[u] = null)
            }
        }
    }
    function tt() {
        return !0
    }
    function nt() {
        return !1
    }
    function rt() {
        try {
            return N.activeElement
        } catch (e) {}
    }
    function it(e) {
        var t = st.split("|"),
            n = e.createDocumentFragment();
        if (n.createElement)
            while (t.length)
                n.createElement(t.pop());
        return n
    }
    function Et(e, t) {
        var n,
            r,
            i = 0,
            s = typeof e.getElementsByTagName !== j ? e.getElementsByTagName(t || "*") : typeof e.querySelectorAll !== j ? e.querySelectorAll(t || "*") : void 0;
        if (!s)
            for (s = [], n = e.childNodes || e; null != (r = n[i]); i++)
                !t || p.nodeName(r, t) ? s.push(r) : p.merge(s, Et(r, t));
        return void 0 === t || t && p.nodeName(e, t) ? p.merge([e], s) : s
    }
    function St(e) {
        K.test(e.type) && (e.defaultChecked = e.checked)
    }
    function xt(e, t) {
        return p.nodeName(e, "table") && p.nodeName(11 !== t.nodeType ? t : t.firstChild, "tr") ? e.getElementsByTagName("tbody")[0] || e.appendChild(e.ownerDocument.createElement("tbody")) : e
    }
    function Tt(e) {
        return e.type = (null !== p.find.attr(e, "type")) + "/" + e.type, e
    }
    function Nt(e) {
        var t = mt.exec(e.type);
        return t ? e.type = t[1] : e.removeAttribute("type"), e
    }
    function Ct(e, t) {
        for (var n, r = 0; null != (n = e[r]); r++)
            p._data(n, "globalEval", !t || p._data(t[r], "globalEval"))
    }
    function kt(e, t) {
        if (1 === t.nodeType && p.hasData(e)) {
            var n,
                r,
                i,
                s = p._data(e),
                o = p._data(t, s),
                u = s.events;
            if (u) {
                delete o.handle, o.events = {};
                for (n in u)
                    for (r = 0, i = u[n].length; i > r; r++)
                        p.event.add(t, n, u[n][r])
            }
            o.data && (o.data = p.extend({}, o.data))
        }
    }
    function Lt(e, t) {
        var n,
            r,
            i;
        if (1 === t.nodeType) {
            if (n = t.nodeName.toLowerCase(), !c.noCloneEvent && t[p.expando]) {
                i = p._data(t);
                for (r in i.events)
                    p.removeEvent(t, r, i.handle);
                t.removeAttribute(p.expando)
            }
            "script" === n && t.text !== e.text ? (Tt(t).text = e.text, Nt(t)) : "object" === n ? (t.parentNode && (t.outerHTML = e.outerHTML), c.html5Clone && e.innerHTML && !p.trim(t.innerHTML) && (t.innerHTML = e.innerHTML)) : "input" === n && K.test(e.type) ? (t.defaultChecked = t.checked = e.checked, t.value !== e.value && (t.value = e.value)) : "option" === n ? t.defaultSelected = t.selected = e.defaultSelected : ("input" === n || "textarea" === n) && (t.defaultValue = e.defaultValue)
        }
    }
    function Mt(t, n) {
        var r = p(n.createElement(t)).appendTo(n.body),
            i = e.getDefaultComputedStyle ? e.getDefaultComputedStyle(r[0]).display : p.css(r[0], "display");
        return r.detach(), i
    }
    function _t(e) {
        var t = N,
            n = Ot[e];
        return n || (n = Mt(e, t), "none" !== n && n || (At = (At || p("<iframe frameborder='0' width='0' height='0'/>")).appendTo(t.documentElement), t = (At[0].contentWindow || At[0].contentDocument).document, t.write(), t.close(), n = Mt(e, t), At.detach()), Ot[e] = n), n
    }
    function Ft(e, t) {
        return {
            get: function() {
                var n = e();
                if (null != n)
                    return n ? void delete this.get : (this.get = t).apply(this, arguments)
            }
        }
    }
    function $t(e, t) {
        if (t in e)
            return t;
        var n = t.charAt(0).toUpperCase() + t.slice(1),
            r = t,
            i = Vt.length;
        while (i--)
            if (t = Vt[i] + n, t in e)
                return t;
        return r
    }
    function Jt(e, t) {
        for (var n, r, i, s = [], o = 0, u = e.length; u > o; o++)
            r = e[o], r.style && (s[o] = p._data(r, "olddisplay"), n = r.style.display, t ? (s[o] || "none" !== n || (r.style.display = ""), "" === r.style.display && $(r) && (s[o] = p._data(r, "olddisplay", _t(r.nodeName)))) : s[o] || (i = $(r), (n && "none" !== n || !i) && p._data(r, "olddisplay", i ? n : p.css(r, "display"))));
        for (o = 0; u > o; o++)
            r = e[o], r.style && (t && "none" !== r.style.display && "" !== r.style.display || (r.style.display = t ? s[o] || "" : "none"));
        return e
    }
    function Kt(e, t, n) {
        var r = Ut.exec(t);
        return r ? Math.max(0, r[1] - (n || 0)) + (r[2] || "px") : t
    }
    function Qt(e, t, n, r, i) {
        for (var s = n === (r ? "border" : "content") ? 4 : "width" === t ? 1 : 0, o = 0; 4 > s; s += 2)
            "margin" === n && (o += p.css(e, n + V[s], !0, i)), r ? ("content" === n && (o -= p.css(e, "padding" + V[s], !0, i)), "margin" !== n && (o -= p.css(e, "border" + V[s] + "Width", !0, i))) : (o += p.css(e, "padding" + V[s], !0, i), "padding" !== n && (o += p.css(e, "border" + V[s] + "Width", !0, i)));
        return o
    }
    function Gt(e, t, n) {
        var r = !0,
            i = "width" === t ? e.offsetWidth : e.offsetHeight,
            s = Ht(e),
            o = c.boxSizing() && "border-box" === p.css(e, "boxSizing", !1, s);
        if (0 >= i || null == i) {
            if (i = Bt(e, t, s), (0 > i || null == i) && (i = e.style[t]), Pt.test(i))
                return i;
            r = o && (c.boxSizingReliable() || i === e.style[t]), i = parseFloat(i) || 0
        }
        return i + Qt(e, t, n || (o ? "border" : "content"), r, s) + "px"
    }
    function Yt(e, t, n, r, i) {
        return new Yt.prototype.init(e, t, n, r, i)
    }
    function un() {
        return setTimeout(function() {
            Zt = void 0
        }), Zt = p.now()
    }
    function an(e, t) {
        var n,
            r = {
                height: e
            },
            i = 0;
        for (t = t ? 1 : 0; 4 > i; i += 2 - t)
            n = V[i], r["margin" + n] = r["padding" + n] = e;
        return t && (r.opacity = r.width = e), r
    }
    function fn(e, t, n) {
        for (var r, i = (on[t] || []).concat(on["*"]), s = 0, o = i.length; o > s; s++)
            if (r = i[s].call(n, t, e))
                return r
    }
    function ln(e, t, n) {
        var r,
            i,
            s,
            o,
            u,
            a,
            f,
            l,
            h = this,
            d = {},
            v = e.style,
            m = e.nodeType && $(e),
            g = p._data(e, "fxshow");
        n.queue || (u = p._queueHooks(e, "fx"), null == u.unqueued && (u.unqueued = 0, a = u.empty.fire, u.empty.fire = function() {
            u.unqueued || a()
        }), u.unqueued++, h.always(function() {
            h.always(function() {
                u.unqueued--, p.queue(e, "fx").length || u.empty.fire()
            })
        })), 1 === e.nodeType && ("height" in t || "width" in t) && (n.overflow = [v.overflow, v.overflowX, v.overflowY], f = p.css(e, "display"), l = _t(e.nodeName), "none" === f && (f = l), "inline" === f && "none" === p.css(e, "float") && (c.inlineBlockNeedsLayout && "inline" !== l ? v.zoom = 1 : v.display = "inline-block")), n.overflow && (v.overflow = "hidden", c.shrinkWrapBlocks() || h.always(function() {
            v.overflow = n.overflow[0], v.overflowX = n.overflow[1], v.overflowY = n.overflow[2]
        }));
        for (r in t)
            if (i = t[r], tn.exec(i)) {
                if (delete t[r], s = s || "toggle" === i, i === (m ? "hide" : "show")) {
                    if ("show" !== i || !g || void 0 === g[r])
                        continue;
                    m = !0
                }
                d[r] = g && g[r] || p.style(e, r)
            }
        if (!p.isEmptyObject(d)) {
            g ? "hidden" in g && (m = g.hidden) : g = p._data(e, "fxshow", {}), s && (g.hidden = !m), m ? p(e).show() : h.done(function() {
                p(e).hide()
            }), h.done(function() {
                var t;
                p._removeData(e, "fxshow");
                for (t in d)
                    p.style(e, t, d[t])
            });
            for (r in d)
                o = fn(m ? g[r] : 0, r, h), r in g || (g[r] = o.start, m && (o.end = o.start, o.start = "width" === r || "height" === r ? 1 : 0))
        }
    }
    function cn(e, t) {
        var n,
            r,
            i,
            s,
            o;
        for (n in e)
            if (r = p.camelCase(n), i = t[r], s = e[n], p.isArray(s) && (i = s[1], s = e[n] = s[0]), n !== r && (e[r] = s, delete e[n]), o = p.cssHooks[r], o && "expand" in o) {
                s = o.expand(s), delete e[r];
                for (n in s)
                    n in e || (e[n] = s[n], t[n] = i)
            } else
                t[r] = i
    }
    function hn(e, t, n) {
        var r,
            i,
            s = 0,
            o = sn.length,
            u = p.Deferred().always(function() {
                delete a.elem
            }),
            a = function() {
                if (i)
                    return !1;
                for (var t = Zt || un(), n = Math.max(0, f.startTime + f.duration - t), r = n / f.duration || 0, s = 1 - r, o = 0, a = f.tweens.length; a > o; o++)
                    f.tweens[o].run(s);
                return u.notifyWith(e, [f, s, n]), 1 > s && a ? n : (u.resolveWith(e, [f]), !1)
            },
            f = u.promise({
                elem: e,
                props: p.extend({}, t),
                opts: p.extend(!0, {
                    specialEasing: {}
                }, n),
                originalProperties: t,
                originalOptions: n,
                startTime: Zt || un(),
                duration: n.duration,
                tweens: [],
                createTween: function(t, n) {
                    var r = p.Tween(e, f.opts, t, n, f.opts.specialEasing[t] || f.opts.easing);
                    return f.tweens.push(r), r
                },
                stop: function(t) {
                    var n = 0,
                        r = t ? f.tweens.length : 0;
                    if (i)
                        return this;
                    for (i = !0; r > n; n++)
                        f.tweens[n].run(1);
                    return t ? u.resolveWith(e, [f, t]) : u.rejectWith(e, [f, t]), this
                }
            }),
            l = f.props;
        for (cn(l, f.opts.specialEasing); o > s; s++)
            if (r = sn[s].call(f, e, l, f.opts))
                return r;
        return p.map(l, fn, f), p.isFunction(f.opts.start) && f.opts.start.call(e, f), p.fx.timer(p.extend(a, {
            elem: e,
            anim: f,
            queue: f.opts.queue
        })), f.progress(f.opts.progress).done(f.opts.done, f.opts.complete).fail(f.opts.fail).always(f.opts.always)
    }
    function In(e) {
        return function(t, n) {
            "string" != typeof t && (n = t, t = "*");
            var r,
                i = 0,
                s = t.toLowerCase().match(M) || [];
            if (p.isFunction(n))
                while (r = s[i++])
                    "+" === r.charAt(0) ? (r = r.slice(1) || "*", (e[r] = e[r] || []).unshift(n)) : (e[r] = e[r] || []).push(n)
        }
    }
    function qn(e, t, n, r) {
        function o(u) {
            var a;
            return i[u] = !0, p.each(e[u] || [], function(e, u) {
                var f = u(t, n, r);
                return "string" != typeof f || s || i[f] ? s ? !(a = f) : void 0 : (t.dataTypes.unshift(f), o(f), !1)
            }), a
        }
        var i = {},
            s = e === Bn;
        return o(t.dataTypes[0]) || !i["*"] && o("*")
    }
    function Rn(e, t) {
        var n,
            r,
            i = p.ajaxSettings.flatOptions || {};
        for (r in t)
            void 0 !== t[r] && ((i[r] ? e : n || (n = {}))[r] = t[r]);
        return n && p.extend(!0, e, n), e
    }
    function Un(e, t, n) {
        var r,
            i,
            s,
            o,
            u = e.contents,
            a = e.dataTypes;
        while ("*" === a[0])
            a.shift(), void 0 === i && (i = e.mimeType || t.getResponseHeader("Content-Type"));
        if (i)
            for (o in u)
                if (u[o] && u[o].test(i)) {
                    a.unshift(o);
                    break
                }
        if (a[0] in n)
            s = a[0];
        else {
            for (o in n) {
                if (!a[0] || e.converters[o + " " + a[0]]) {
                    s = o;
                    break
                }
                r || (r = o)
            }
            s = s || r
        }
        return s ? (s !== a[0] && a.unshift(s), n[s]) : void 0
    }
    function zn(e, t, n, r) {
        var i,
            s,
            o,
            u,
            a,
            f = {},
            l = e.dataTypes.slice();
        if (l[1])
            for (o in e.converters)
                f[o.toLowerCase()] = e.converters[o];
        s = l.shift();
        while (s)
            if (e.responseFields[s] && (n[e.responseFields[s]] = t), !a && r && e.dataFilter && (t = e.dataFilter(t, e.dataType)), a = s, s = l.shift())
                if ("*" === s)
                    s = a;
                else if ("*" !== a && a !== s) {
                    if (o = f[a + " " + s] || f["* " + s], !o)
                        for (i in f)
                            if (u = i.split(" "), u[1] === s && (o = f[a + " " + u[0]] || f["* " + u[0]])) {
                                o === !0 ? o = f[i] : f[i] !== !0 && (s = u[0], l.unshift(u[1]));
                                break
                            }
                    if (o !== !0)
                        if (o && e["throws"])
                            t = o(t);
                        else
                            try {
                                t = o(t)
                            } catch (c) {
                                return {
                                    state: "parsererror",
                                    error: o ? c : "No conversion from " + a + " to " + s
                                }
                            }
                }
        return {
            state: "success",
            data: t
        }
    }
    function Kn(e, t, n, r) {
        var i;
        if (p.isArray(t))
            p.each(t, function(t, i) {
                n || Xn.test(e) ? r(e, i) : Kn(e + "[" + ("object" == typeof i ? t : "") + "]", i, n, r)
            });
        else if (n || "object" !== p.type(t))
            r(e, t);
        else
            for (i in t)
                Kn(e + "[" + i + "]", t[i], n, r)
    }
    function Zn() {
        try {
            return new e.XMLHttpRequest
        } catch (t) {}
    }
    function er() {
        try {
            return new e.ActiveXObject("Microsoft.XMLHTTP")
        } catch (t) {}
    }
    function sr(e) {
        return p.isWindow(e) ? e : 9 === e.nodeType ? e.defaultView || e.parentWindow : !1
    }
    var n = [],
        r = n.slice,
        i = n.concat,
        s = n.push,
        o = n.indexOf,
        u = {},
        a = u.toString,
        f = u.hasOwnProperty,
        l = "".trim,
        c = {},
        h = "1.11.0",
        p = function(e, t) {
            return new p.fn.init(e, t)
        },
        d = /^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,
        v = /^-ms-/,
        m = /-([\da-z])/gi,
        g = function(e, t) {
            return t.toUpperCase()
        };
    p.fn = p.prototype = {
        jquery: h,
        constructor: p,
        selector: "",
        length: 0,
        toArray: function() {
            return r.call(this)
        },
        get: function(e) {
            return null != e ? 0 > e ? this[e + this.length] : this[e] : r.call(this)
        },
        pushStack: function(e) {
            var t = p.merge(this.constructor(), e);
            return t.prevObject = this, t.context = this.context, t
        },
        each: function(e, t) {
            return p.each(this, e, t)
        },
        map: function(e) {
            return this.pushStack(p.map(this, function(t, n) {
                return e.call(t, n, t)
            }))
        },
        slice: function() {
            return this.pushStack(r.apply(this, arguments))
        },
        first: function() {
            return this.eq(0)
        },
        last: function() {
            return this.eq(-1)
        },
        eq: function(e) {
            var t = this.length,
                n = +e + (0 > e ? t : 0);
            return this.pushStack(n >= 0 && t > n ? [this[n]] : [])
        },
        end: function() {
            return this.prevObject || this.constructor(null)
        },
        push: s,
        sort: n.sort,
        splice: n.splice
    }, p.extend = p.fn.extend = function() {
        var e,
            t,
            n,
            r,
            i,
            s,
            o = arguments[0] || {},
            u = 1,
            a = arguments.length,
            f = !1;
        for ("boolean" == typeof o && (f = o, o = arguments[u] || {}, u++), "object" == typeof o || p.isFunction(o) || (o = {}), u === a && (o = this, u--); a > u; u++)
            if (null != (i = arguments[u]))
                for (r in i)
                    e = o[r], n = i[r], o !== n && (f && n && (p.isPlainObject(n) || (t = p.isArray(n))) ? (t ? (t = !1, s = e && p.isArray(e) ? e : []) : s = e && p.isPlainObject(e) ? e : {}, o[r] = p.extend(f, s, n)) : void 0 !== n && (o[r] = n));
        return o
    }, p.extend({
        expando: "jQuery" + (h + Math.random()).replace(/\D/g, ""),
        isReady: !0,
        error: function(e) {
            throw new Error(e)
        },
        noop: function() {},
        isFunction: function(e) {
            return "function" === p.type(e)
        },
        isArray: Array.isArray || function(e) {
            return "array" === p.type(e)
        },
        isWindow: function(e) {
            return null != e && e == e.window
        },
        isNumeric: function(e) {
            return e - parseFloat(e) >= 0
        },
        isEmptyObject: function(e) {
            var t;
            for (t in e)
                return !1;
            return !0
        },
        isPlainObject: function(e) {
            var t;
            if (!e || "object" !== p.type(e) || e.nodeType || p.isWindow(e))
                return !1;
            try {
                if (e.constructor && !f.call(e, "constructor") && !f.call(e.constructor.prototype, "isPrototypeOf"))
                    return !1
            } catch (n) {
                return !1
            }
            if (c.ownLast)
                for (t in e)
                    return f.call(e, t);
            for (t in e)
                ;
            return void 0 === t || f.call(e, t)
        },
        type: function(e) {
            return null == e ? e + "" : "object" == typeof e || "function" == typeof e ? u[a.call(e)] || "object" : typeof e
        },
        globalEval: function(t) {
            t && p.trim(t) && (e.execScript || function(t) {
                e.eval.call(e, t)
            })(t)
        },
        camelCase: function(e) {
            return e.replace(v, "ms-").replace(m, g)
        },
        nodeName: function(e, t) {
            return e.nodeName && e.nodeName.toLowerCase() === t.toLowerCase()
        },
        each: function(e, t, n) {
            var r,
                i = 0,
                s = e.length,
                o = y(e);
            if (n) {
                if (o) {
                    for (; s > i; i++)
                        if (r = t.apply(e[i], n), r === !1)
                            break
                } else
                    for (i in e)
                        if (r = t.apply(e[i], n), r === !1)
                            break
            } else if (o) {
                for (; s > i; i++)
                    if (r = t.call(e[i], i, e[i]), r === !1)
                        break
            } else
                for (i in e)
                    if (r = t.call(e[i], i, e[i]), r === !1)
                        break;
            return e
        },
        trim: l && !l.call("﻿ ") ? function(e) {
            return null == e ? "" : l.call(e)
        } : function(e) {
            return null == e ? "" : (e + "").replace(d, "")
        },
        makeArray: function(e, t) {
            var n = t || [];
            return null != e && (y(Object(e)) ? p.merge(n, "string" == typeof e ? [e] : e) : s.call(n, e)), n
        },
        inArray: function(e, t, n) {
            var r;
            if (t) {
                if (o)
                    return o.call(t, e, n);
                for (r = t.length, n = n ? 0 > n ? Math.max(0, r + n) : n : 0; r > n; n++)
                    if (n in t && t[n] === e)
                        return n
            }
            return -1
        },
        merge: function(e, t) {
            var n = +t.length,
                r = 0,
                i = e.length;
            while (n > r)
                e[i++] = t[r++];
            if (n !== n)
                while (void 0 !== t[r])
                    e[i++] = t[r++];
            return e.length = i, e
        },
        grep: function(e, t, n) {
            for (var r, i = [], s = 0, o = e.length, u = !n; o > s; s++)
                r = !t(e[s], s), r !== u && i.push(e[s]);
            return i
        },
        map: function(e, t, n) {
            var r,
                s = 0,
                o = e.length,
                u = y(e),
                a = [];
            if (u)
                for (; o > s; s++)
                    r = t(e[s], s, n), null != r && a.push(r);
            else
                for (s in e)
                    r = t(e[s], s, n), null != r && a.push(r);
            return i.apply([], a)
        },
        guid: 1,
        proxy: function(e, t) {
            var n,
                i,
                s;
            return "string" == typeof t && (s = e[t], t = e, e = s), p.isFunction(e) ? (n = r.call(arguments, 2), i = function() {
                return e.apply(t || this, n.concat(r.call(arguments)))
            }, i.guid = e.guid = e.guid || p.guid++, i) : void 0
        },
        now: function() {
            return +(new Date)
        },
        support: c
    }), p.each("Boolean Number String Function Array Date RegExp Object Error".split(" "), function(e, t) {
        u["[object " + t + "]"] = t.toLowerCase()
    });
    var b = function(e) {
        function rt(e, t, r, i) {
            var s,
                o,
                u,
                a,
                f,
                h,
                v,
                m,
                w,
                E;
            if ((t ? t.ownerDocument || t : b) !== c && l(t), t = t || c, r = r || [], !e || "string" != typeof e)
                return r;
            if (1 !== (a = t.nodeType) && 9 !== a)
                return [];
            if (p && !i) {
                if (s = G.exec(e))
                    if (u = s[1]) {
                        if (9 === a) {
                            if (o = t.getElementById(u), !o || !o.parentNode)
                                return r;
                            if (o.id === u)
                                return r.push(o), r
                        } else if (t.ownerDocument && (o = t.ownerDocument.getElementById(u)) && g(t, o) && o.id === u)
                            return r.push(o), r
                    } else {
                        if (s[2])
                            return _.apply(r, t.getElementsByTagName(e)), r;
                        if ((u = s[3]) && n.getElementsByClassName && t.getElementsByClassName)
                            return _.apply(r, t.getElementsByClassName(u)), r
                    }
                if (n.qsa && (!d || !d.test(e))) {
                    if (m = v = y, w = t, E = 9 === a && e, 1 === a && "object" !== t.nodeName.toLowerCase()) {
                        h = dt(e), (v = t.getAttribute("id")) ? m = v.replace(Z, "\\$&") : t.setAttribute("id", m), m = "[id='" + m + "'] ", f = h.length;
                        while (f--)
                            h[f] = m + vt(h[f]);
                        w = Y.test(e) && ht(t.parentNode) || t, E = h.join(",")
                    }
                    if (E)
                        try {
                            return _.apply(r, w.querySelectorAll(E)), r
                        } catch (S) {} finally {
                            v || t.removeAttribute("id")
                        }
                }
            }
            return xt(e.replace(R, "$1"), t, r, i)
        }
        function it() {
            function t(n, i) {
                return e.push(n + " ") > r.cacheLength && delete t[e.shift()], t[n + " "] = i
            }
            var e = [];
            return t
        }
        function st(e) {
            return e[y] = !0, e
        }
        function ot(e) {
            var t = c.createElement("div");
            try {
                return !!e(t)
            } catch (n) {
                return !1
            } finally {
                t.parentNode && t.parentNode.removeChild(t), t = null
            }
        }
        function ut(e, t) {
            var n = e.split("|"),
                i = e.length;
            while (i--)
                r.attrHandle[n[i]] = t
        }
        function at(e, t) {
            var n = t && e,
                r = n && 1 === e.nodeType && 1 === t.nodeType && (~t.sourceIndex || k) - (~e.sourceIndex || k);
            if (r)
                return r;
            if (n)
                while (n = n.nextSibling)
                    if (n === t)
                        return -1;
            return e ? 1 : -1
        }
        function ft(e) {
            return function(t) {
                var n = t.nodeName.toLowerCase();
                return "input" === n && t.type === e
            }
        }
        function lt(e) {
            return function(t) {
                var n = t.nodeName.toLowerCase();
                return ("input" === n || "button" === n) && t.type === e
            }
        }
        function ct(e) {
            return st(function(t) {
                return t = +t, st(function(n, r) {
                    var i,
                        s = e([], n.length, t),
                        o = s.length;
                    while (o--)
                        n[i = s[o]] && (n[i] = !(r[i] = n[i]))
                })
            })
        }
        function ht(e) {
            return e && typeof e.getElementsByTagName !== C && e
        }
        function pt() {}
        function dt(e, t) {
            var n,
                i,
                s,
                o,
                u,
                a,
                f,
                l = x[e + " "];
            if (l)
                return t ? 0 : l.slice(0);
            u = e, a = [], f = r.preFilter;
            while (u) {
                (!n || (i = U.exec(u))) && (i && (u = u.slice(i[0].length) || u), a.push(s = [])), n = !1, (i = z.exec(u)) && (n = i.shift(), s.push({
                    value: n,
                    type: i[0].replace(R, " ")
                }), u = u.slice(n.length));
                for (o in r.filter)
                    !(i = $[o].exec(u)) || f[o] && !(i = f[o](i)) || (n = i.shift(), s.push({
                        value: n,
                        type: o,
                        matches: i
                    }), u = u.slice(n.length));
                if (!n)
                    break
            }
            return t ? u.length : u ? rt.error(e) : x(e, a).slice(0)
        }
        function vt(e) {
            for (var t = 0, n = e.length, r = ""; n > t; t++)
                r += e[t].value;
            return r
        }
        function mt(e, t, n) {
            var r = t.dir,
                i = n && "parentNode" === r,
                s = E++;
            return t.first ? function(t, n, s) {
                while (t = t[r])
                    if (1 === t.nodeType || i)
                        return e(t, n, s)
            } : function(t, n, o) {
                var u,
                    a,
                    f = [w, s];
                if (o) {
                    while (t = t[r])
                        if ((1 === t.nodeType || i) && e(t, n, o))
                            return !0
                } else
                    while (t = t[r])
                        if (1 === t.nodeType || i) {
                            if (a = t[y] || (t[y] = {}), (u = a[r]) && u[0] === w && u[1] === s)
                                return f[2] = u[2];
                            if (a[r] = f, f[2] = e(t, n, o))
                                return !0
                        }
            }
        }
        function gt(e) {
            return e.length > 1 ? function(t, n, r) {
                var i = e.length;
                while (i--)
                    if (!e[i](t, n, r))
                        return !1;
                return !0
            } : e[0]
        }
        function yt(e, t, n, r, i) {
            for (var s, o = [], u = 0, a = e.length, f = null != t; a > u; u++)
                (s = e[u]) && (!n || n(s, r, i)) && (o.push(s), f && t.push(u));
            return o
        }
        function bt(e, t, n, r, i, s) {
            return r && !r[y] && (r = bt(r)), i && !i[y] && (i = bt(i, s)), st(function(s, o, u, a) {
                var f,
                    l,
                    c,
                    h = [],
                    p = [],
                    d = o.length,
                    v = s || St(t || "*", u.nodeType ? [u] : u, []),
                    m = !e || !s && t ? v : yt(v, h, e, u, a),
                    g = n ? i || (s ? e : d || r) ? [] : o : m;
                if (n && n(m, g, u, a), r) {
                    f = yt(g, p), r(f, [], u, a), l = f.length;
                    while (l--)
                        (c = f[l]) && (g[p[l]] = !(m[p[l]] = c))
                }
                if (s) {
                    if (i || e) {
                        if (i) {
                            f = [], l = g.length;
                            while (l--)
                                (c = g[l]) && f.push(m[l] = c);
                            i(null, g = [], f, a)
                        }
                        l = g.length;
                        while (l--)
                            (c = g[l]) && (f = i ? P.call(s, c) : h[l]) > -1 && (s[f] = !(o[f] = c))
                    }
                } else
                    g = yt(g === o ? g.splice(d, g.length) : g), i ? i(null, o, g, a) : _.apply(o, g)
            })
        }
        function wt(e) {
            for (var t, n, i, s = e.length, o = r.relative[e[0].type], a = o || r.relative[" "], f = o ? 1 : 0, l = mt(function(e) {
                    return e === t
                }, a, !0), c = mt(function(e) {
                    return P.call(t, e) > -1
                }, a, !0), h = [function(e, n, r) {
                    return !o && (r || n !== u) || ((t = n).nodeType ? l(e, n, r) : c(e, n, r))
                }]; s > f; f++)
                if (n = r.relative[e[f].type])
                    h = [mt(gt(h), n)];
                else {
                    if (n = r.filter[e[f].type].apply(null, e[f].matches), n[y]) {
                        for (i = ++f; s > i; i++)
                            if (r.relative[e[i].type])
                                break;
                        return bt(f > 1 && gt(h), f > 1 && vt(e.slice(0, f - 1).concat({
                            value: " " === e[f - 2].type ? "*" : ""
                        })).replace(R, "$1"), n, i > f && wt(e.slice(f, i)), s > i && wt(e = e.slice(i)), s > i && vt(e))
                    }
                    h.push(n)
                }
            return gt(h)
        }
        function Et(e, t) {
            var n = t.length > 0,
                i = e.length > 0,
                s = function(s, o, a, f, l) {
                    var h,
                        p,
                        d,
                        v = 0,
                        m = "0",
                        g = s && [],
                        y = [],
                        b = u,
                        E = s || i && r.find.TAG("*", l),
                        S = w += null == b ? 1 : Math.random() || .1,
                        x = E.length;
                    for (l && (u = o !== c && o); m !== x && null != (h = E[m]); m++) {
                        if (i && h) {
                            p = 0;
                            while (d = e[p++])
                                if (d(h, o, a)) {
                                    f.push(h);
                                    break
                                }
                            l && (w = S)
                        }
                        n && ((h = !d && h) && v--, s && g.push(h))
                    }
                    if (v += m, n && m !== v) {
                        p = 0;
                        while (d = t[p++])
                            d(g, y, o, a);
                        if (s) {
                            if (v > 0)
                                while (m--)
                                    g[m] || y[m] || (y[m] = O.call(f));
                            y = yt(y)
                        }
                        _.apply(f, y), l && !s && y.length > 0 && v + t.length > 1 && rt.uniqueSort(f)
                    }
                    return l && (w = S, u = b), g
                };
            return n ? st(s) : s
        }
        function St(e, t, n) {
            for (var r = 0, i = t.length; i > r; r++)
                rt(e, t[r], n);
            return n
        }
        function xt(e, t, i, s) {
            var u,
                a,
                f,
                l,
                c,
                h = dt(e);
            if (!s && 1 === h.length) {
                if (a = h[0] = h[0].slice(0), a.length > 2 && "ID" === (f = a[0]).type && n.getById && 9 === t.nodeType && p && r.relative[a[1].type]) {
                    if (t = (r.find.ID(f.matches[0].replace(et, tt), t) || [])[0], !t)
                        return i;
                    e = e.slice(a.shift().value.length)
                }
                u = $.needsContext.test(e) ? 0 : a.length;
                while (u--) {
                    if (f = a[u], r.relative[l = f.type])
                        break;
                    if ((c = r.find[l]) && (s = c(f.matches[0].replace(et, tt), Y.test(a[0].type) && ht(t.parentNode) || t))) {
                        if (a.splice(u, 1), e = s.length && vt(a), !e)
                            return _.apply(i, s), i;
                        break
                    }
                }
            }
            return o(e, h)(s, t, !p, i, Y.test(e) && ht(t.parentNode) || t), i
        }
        var t,
            n,
            r,
            i,
            s,
            o,
            u,
            a,
            f,
            l,
            c,
            h,
            p,
            d,
            v,
            m,
            g,
            y = "sizzle" + -(new Date),
            b = e.document,
            w = 0,
            E = 0,
            S = it(),
            x = it(),
            T = it(),
            N = function(e, t) {
                return e === t && (f = !0), 0
            },
            C = "undefined",
            k = 1 << 31,
            L = {}.hasOwnProperty,
            A = [],
            O = A.pop,
            M = A.push,
            _ = A.push,
            D = A.slice,
            P = A.indexOf || function(e) {
                for (var t = 0, n = this.length; n > t; t++)
                    if (this[t] === e)
                        return t;
                return -1
            },
            H = "checked|selected|async|autofocus|autoplay|controls|defer|disabled|hidden|ismap|loop|multiple|open|readonly|required|scoped",
            B = "[\\x20\\t\\r\\n\\f]",
            j = "(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+",
            F = j.replace("w", "w#"),
            I = "\\[" + B + "*(" + j + ")" + B + "*(?:([*^$|!~]?=)" + B + "*(?:(['\"])((?:\\\\.|[^\\\\])*?)\\3|(" + F + ")|)|)" + B + "*\\]",
            q = ":(" + j + ")(?:\\(((['\"])((?:\\\\.|[^\\\\])*?)\\3|((?:\\\\.|[^\\\\()[\\]]|" + I.replace(3, 8) + ")*)|.*)\\)|)",
            R = new RegExp("^" + B + "+|((?:^|[^\\\\])(?:\\\\.)*)" + B + "+$", "g"),
            U = new RegExp("^" + B + "*," + B + "*"),
            z = new RegExp("^" + B + "*([>+~]|" + B + ")" + B + "*"),
            W = new RegExp("=" + B + "*([^\\]'\"]*?)" + B + "*\\]", "g"),
            X = new RegExp(q),
            V = new RegExp("^" + F + "$"),
            $ = {
                ID: new RegExp("^#(" + j + ")"),
                CLASS: new RegExp("^\\.(" + j + ")"),
                TAG: new RegExp("^(" + j.replace("w", "w*") + ")"),
                ATTR: new RegExp("^" + I),
                PSEUDO: new RegExp("^" + q),
                CHILD: new RegExp("^:(only|first|last|nth|nth-last)-(child|of-type)(?:\\(" + B + "*(even|odd|(([+-]|)(\\d*)n|)" + B + "*(?:([+-]|)" + B + "*(\\d+)|))" + B + "*\\)|)", "i"),
                bool: new RegExp("^(?:" + H + ")$", "i"),
                needsContext: new RegExp("^" + B + "*[>+~]|:(even|odd|eq|gt|lt|nth|first|last)(?:\\(" + B + "*((?:-\\d)?\\d*)" + B + "*\\)|)(?=[^-]|$)", "i")
            },
            J = /^(?:input|select|textarea|button)$/i,
            K = /^h\d$/i,
            Q = /^[^{]+\{\s*\[native \w/,
            G = /^(?:#([\w-]+)|(\w+)|\.([\w-]+))$/,
            Y = /[+~]/,
            Z = /'|\\/g,
            et = new RegExp("\\\\([\\da-f]{1,6}" + B + "?|(" + B + ")|.)", "ig"),
            tt = function(e, t, n) {
                var r = "0x" + t - 65536;
                return r !== r || n ? t : 0 > r ? String.fromCharCode(r + 65536) : String.fromCharCode(r >> 10 | 55296, 1023 & r | 56320)
            };
        try {
            _.apply(A = D.call(b.childNodes), b.childNodes), A[b.childNodes.length].nodeType
        } catch (nt) {
            _ = {
                apply: A.length ? function(e, t) {
                    M.apply(e, D.call(t))
                } : function(e, t) {
                    var n = e.length,
                        r = 0;
                    while (e[n++] = t[r++])
                        ;
                    e.length = n - 1
                }
            }
        }
        n = rt.support = {}, s = rt.isXML = function(e) {
            var t = e && (e.ownerDocument || e).documentElement;
            return t ? "HTML" !== t.nodeName : !1
        }, l = rt.setDocument = function(e) {
            var t,
                i = e ? e.ownerDocument || e : b,
                o = i.defaultView;
            return i !== c && 9 === i.nodeType && i.documentElement ? (c = i, h = i.documentElement, p = !s(i), o && o !== o.top && (o.addEventListener ? o.addEventListener("unload", function() {
                l()
            }, !1) : o.attachEvent && o.attachEvent("onunload", function() {
                l()
            })), n.attributes = ot(function(e) {
                return e.className = "i", !e.getAttribute("className")
            }), n.getElementsByTagName = ot(function(e) {
                return e.appendChild(i.createComment("")), !e.getElementsByTagName("*").length
            }), n.getElementsByClassName = Q.test(i.getElementsByClassName) && ot(function(e) {
                return e.innerHTML = "<div class='a'></div><div class='a i'></div>", e.firstChild.className = "i", 2 === e.getElementsByClassName("i").length
            }), n.getById = ot(function(e) {
                return h.appendChild(e).id = y, !i.getElementsByName || !i.getElementsByName(y).length
            }), n.getById ? (r.find.ID = function(e, t) {
                if (typeof t.getElementById !== C && p) {
                    var n = t.getElementById(e);
                    return n && n.parentNode ? [n] : []
                }
            }, r.filter.ID = function(e) {
                var t = e.replace(et, tt);
                return function(e) {
                    return e.getAttribute("id") === t
                }
            }) : (delete r.find.ID, r.filter.ID = function(e) {
                var t = e.replace(et, tt);
                return function(e) {
                    var n = typeof e.getAttributeNode !== C && e.getAttributeNode("id");
                    return n && n.value === t
                }
            }), r.find.TAG = n.getElementsByTagName ? function(e, t) {
                return typeof t.getElementsByTagName !== C ? t.getElementsByTagName(e) : void 0
            } : function(e, t) {
                var n,
                    r = [],
                    i = 0,
                    s = t.getElementsByTagName(e);
                if ("*" === e) {
                    while (n = s[i++])
                        1 === n.nodeType && r.push(n);
                    return r
                }
                return s
            }, r.find.CLASS = n.getElementsByClassName && function(e, t) {
                return typeof t.getElementsByClassName !== C && p ? t.getElementsByClassName(e) : void 0
            }, v = [], d = [], (n.qsa = Q.test(i.querySelectorAll)) && (ot(function(e) {
                e.innerHTML = "<select t=''><option selected=''></option></select>", e.querySelectorAll("[t^='']").length && d.push("[*^$]=" + B + "*(?:''|\"\")"), e.querySelectorAll("[selected]").length || d.push("\\[" + B + "*(?:value|" + H + ")"), e.querySelectorAll(":checked").length || d.push(":checked")
            }), ot(function(e) {
                var t = i.createElement("input");
                t.setAttribute("type", "hidden"), e.appendChild(t).setAttribute("name", "D"), e.querySelectorAll("[name=d]").length && d.push("name" + B + "*[*^$|!~]?="), e.querySelectorAll(":enabled").length || d.push(":enabled", ":disabled"), e.querySelectorAll("*,:x"), d.push(",.*:")
            })), (n.matchesSelector = Q.test(m = h.webkitMatchesSelector || h.mozMatchesSelector || h.oMatchesSelector || h.msMatchesSelector)) && ot(function(e) {
                n.disconnectedMatch = m.call(e, "div"), m.call(e, "[s!='']:x"), v.push("!=", q)
            }), d = d.length && new RegExp(d.join("|")), v = v.length && new RegExp(v.join("|")), t = Q.test(h.compareDocumentPosition), g = t || Q.test(h.contains) ? function(e, t) {
                var n = 9 === e.nodeType ? e.documentElement : e,
                    r = t && t.parentNode;
                return e === r || !!r && 1 === r.nodeType && !!(n.contains ? n.contains(r) : e.compareDocumentPosition && 16 & e.compareDocumentPosition(r))
            } : function(e, t) {
                if (t)
                    while (t = t.parentNode)
                        if (t === e)
                            return !0;
                return !1
            }, N = t ? function(e, t) {
                if (e === t)
                    return f = !0, 0;
                var r = !e.compareDocumentPosition - !t.compareDocumentPosition;
                return r ? r : (r = (e.ownerDocument || e) === (t.ownerDocument || t) ? e.compareDocumentPosition(t) : 1, 1 & r || !n.sortDetached && t.compareDocumentPosition(e) === r ? e === i || e.ownerDocument === b && g(b, e) ? -1 : t === i || t.ownerDocument === b && g(b, t) ? 1 : a ? P.call(a, e) - P.call(a, t) : 0 : 4 & r ? -1 : 1)
            } : function(e, t) {
                if (e === t)
                    return f = !0, 0;
                var n,
                    r = 0,
                    s = e.parentNode,
                    o = t.parentNode,
                    u = [e],
                    l = [t];
                if (!s || !o)
                    return e === i ? -1 : t === i ? 1 : s ? -1 : o ? 1 : a ? P.call(a, e) - P.call(a, t) : 0;
                if (s === o)
                    return at(e, t);
                n = e;
                while (n = n.parentNode)
                    u.unshift(n);
                n = t;
                while (n = n.parentNode)
                    l.unshift(n);
                while (u[r] === l[r])
                    r++;
                return r ? at(u[r], l[r]) : u[r] === b ? -1 : l[r] === b ? 1 : 0
            }, i) : c
        }, rt.matches = function(e, t) {
            return rt(e, null, null, t)
        }, rt.matchesSelector = function(e, t) {
            if ((e.ownerDocument || e) !== c && l(e), t = t.replace(W, "='$1']"), !(!n.matchesSelector || !p || v && v.test(t) || d && d.test(t)))
                try {
                    var r = m.call(e, t);
                    if (r || n.disconnectedMatch || e.document && 11 !== e.document.nodeType)
                        return r
                } catch (i) {}
            return rt(t, c, null, [e]).length > 0
        }, rt.contains = function(e, t) {
            return (e.ownerDocument || e) !== c && l(e), g(e, t)
        }, rt.attr = function(e, t) {
            (e.ownerDocument || e) !== c && l(e);
            var i = r.attrHandle[t.toLowerCase()],
                s = i && L.call(r.attrHandle, t.toLowerCase()) ? i(e, t, !p) : void 0;
            return void 0 !== s ? s : n.attributes || !p ? e.getAttribute(t) : (s = e.getAttributeNode(t)) && s.specified ? s.value : null
        }, rt.error = function(e) {
            throw new Error("Syntax error, unrecognized expression: " + e)
        }, rt.uniqueSort = function(e) {
            var t,
                r = [],
                i = 0,
                s = 0;
            if (f = !n.detectDuplicates, a = !n.sortStable && e.slice(0), e.sort(N), f) {
                while (t = e[s++])
                    t === e[s] && (i = r.push(s));
                while (i--)
                    e.splice(r[i], 1)
            }
            return a = null, e
        }, i = rt.getText = function(e) {
            var t,
                n = "",
                r = 0,
                s = e.nodeType;
            if (s) {
                if (1 === s || 9 === s || 11 === s) {
                    if ("string" == typeof e.textContent)
                        return e.textContent;
                    for (e = e.firstChild; e; e = e.nextSibling)
                        n += i(e)
                } else if (3 === s || 4 === s)
                    return e.nodeValue
            } else
                while (t = e[r++])
                    n += i(t);
            return n
        }, r = rt.selectors = {
            cacheLength: 50,
            createPseudo: st,
            match: $,
            attrHandle: {},
            find: {},
            relative: {
                ">": {
                    dir: "parentNode",
                    first: !0
                },
                " ": {
                    dir: "parentNode"
                },
                "+": {
                    dir: "previousSibling",
                    first: !0
                },
                "~": {
                    dir: "previousSibling"
                }
            },
            preFilter: {
                ATTR: function(e) {
                    return e[1] = e[1].replace(et, tt), e[3] = (e[4] || e[5] || "").replace(et, tt), "~=" === e[2] && (e[3] = " " + e[3] + " "), e.slice(0, 4)
                },
                CHILD: function(e) {
                    return e[1] = e[1].toLowerCase(), "nth" === e[1].slice(0, 3) ? (e[3] || rt.error(e[0]), e[4] = +(e[4] ? e[5] + (e[6] || 1) : 2 * ("even" === e[3] || "odd" === e[3])), e[5] = +(e[7] + e[8] || "odd" === e[3])) : e[3] && rt.error(e[0]), e
                },
                PSEUDO: function(e) {
                    var t,
                        n = !e[5] && e[2];
                    return $.CHILD.test(e[0]) ? null : (e[3] && void 0 !== e[4] ? e[2] = e[4] : n && X.test(n) && (t = dt(n, !0)) && (t = n.indexOf(")", n.length - t) - n.length) && (e[0] = e[0].slice(0, t), e[2] = n.slice(0, t)), e.slice(0, 3))
                }
            },
            filter: {
                TAG: function(e) {
                    var t = e.replace(et, tt).toLowerCase();
                    return "*" === e ? function() {
                        return !0
                    } : function(e) {
                        return e.nodeName && e.nodeName.toLowerCase() === t
                    }
                },
                CLASS: function(e) {
                    var t = S[e + " "];
                    return t || (t = new RegExp("(^|" + B + ")" + e + "(" + B + "|$)")) && S(e, function(e) {
                            return t.test("string" == typeof e.className && e.className || typeof e.getAttribute !== C && e.getAttribute("class") || "")
                        })
                },
                ATTR: function(e, t, n) {
                    return function(r) {
                        var i = rt.attr(r, e);
                        return null == i ? "!=" === t : t ? (i += "", "=" === t ? i === n : "!=" === t ? i !== n : "^=" === t ? n && 0 === i.indexOf(n) : "*=" === t ? n && i.indexOf(n) > -1 : "$=" === t ? n && i.slice(-n.length) === n : "~=" === t ? (" " + i + " ").indexOf(n) > -1 : "|=" === t ? i === n || i.slice(0, n.length + 1) === n + "-" : !1) : !0
                    }
                },
                CHILD: function(e, t, n, r, i) {
                    var s = "nth" !== e.slice(0, 3),
                        o = "last" !== e.slice(-4),
                        u = "of-type" === t;
                    return 1 === r && 0 === i ? function(e) {
                        return !!e.parentNode
                    } : function(t, n, a) {
                        var f,
                            l,
                            c,
                            h,
                            p,
                            d,
                            v = s !== o ? "nextSibling" : "previousSibling",
                            m = t.parentNode,
                            g = u && t.nodeName.toLowerCase(),
                            b = !a && !u;
                        if (m) {
                            if (s) {
                                while (v) {
                                    c = t;
                                    while (c = c[v])
                                        if (u ? c.nodeName.toLowerCase() === g : 1 === c.nodeType)
                                            return !1;
                                    d = v = "only" === e && !d && "nextSibling"
                                }
                                return !0
                            }
                            if (d = [o ? m.firstChild : m.lastChild], o && b) {
                                l = m[y] || (m[y] = {}), f = l[e] || [], p = f[0] === w && f[1], h = f[0] === w && f[2], c = p && m.childNodes[p];
                                while (c = ++p && c && c[v] || (h = p = 0) || d.pop())
                                    if (1 === c.nodeType && ++h && c === t) {
                                        l[e] = [w, p, h];
                                        break
                                    }
                            } else if (b && (f = (t[y] || (t[y] = {}))[e]) && f[0] === w)
                                h = f[1];
                            else
                                while (c = ++p && c && c[v] || (h = p = 0) || d.pop())
                                    if ((u ? c.nodeName.toLowerCase() === g : 1 === c.nodeType) && ++h && (b && ((c[y] || (c[y] = {}))[e] = [w, h]), c === t))
                                        break;
                            return h -= i, h === r || h % r === 0 && h / r >= 0
                        }
                    }
                },
                PSEUDO: function(e, t) {
                    var n,
                        i = r.pseudos[e] || r.setFilters[e.toLowerCase()] || rt.error("unsupported pseudo: " + e);
                    return i[y] ? i(t) : i.length > 1 ? (n = [e, e, "", t], r.setFilters.hasOwnProperty(e.toLowerCase()) ? st(function(e, n) {
                        var r,
                            s = i(e, t),
                            o = s.length;
                        while (o--)
                            r = P.call(e, s[o]), e[r] = !(n[r] = s[o])
                    }) : function(e) {
                        return i(e, 0, n)
                    }) : i
                }
            },
            pseudos: {
                not: st(function(e) {
                    var t = [],
                        n = [],
                        r = o(e.replace(R, "$1"));
                    return r[y] ? st(function(e, t, n, i) {
                        var s,
                            o = r(e, null, i, []),
                            u = e.length;
                        while (u--)
                            (s = o[u]) && (e[u] = !(t[u] = s))
                    }) : function(e, i, s) {
                        return t[0] = e, r(t, null, s, n), !n.pop()
                    }
                }),
                has: st(function(e) {
                    return function(t) {
                        return rt(e, t).length > 0
                    }
                }),
                contains: st(function(e) {
                    return function(t) {
                        return (t.textContent || t.innerText || i(t)).indexOf(e) > -1
                    }
                }),
                lang: st(function(e) {
                    return V.test(e || "") || rt.error("unsupported lang: " + e), e = e.replace(et, tt).toLowerCase(), function(t) {
                        var n;
                        do if (n = p ? t.lang : t.getAttribute("xml:lang") || t.getAttribute("lang"))
                            return n = n.toLowerCase(), n === e || 0 === n.indexOf(e + "-");
                        while ((t = t.parentNode) && 1 === t.nodeType);
                        return !1
                    }
                }),
                target: function(t) {
                    var n = e.location && e.location.hash;
                    return n && n.slice(1) === t.id
                },
                root: function(e) {
                    return e === h
                },
                focus: function(e) {
                    return e === c.activeElement && (!c.hasFocus || c.hasFocus()) && !!(e.type || e.href || ~e.tabIndex)
                },
                enabled: function(e) {
                    return e.disabled === !1
                },
                disabled: function(e) {
                    return e.disabled === !0
                },
                checked: function(e) {
                    var t = e.nodeName.toLowerCase();
                    return "input" === t && !!e.checked || "option" === t && !!e.selected
                },
                selected: function(e) {
                    return e.parentNode && e.parentNode.selectedIndex, e.selected === !0
                },
                empty: function(e) {
                    for (e = e.firstChild; e; e = e.nextSibling)
                        if (e.nodeType < 6)
                            return !1;
                    return !0
                },
                parent: function(e) {
                    return !r.pseudos.empty(e)
                },
                header: function(e) {
                    return K.test(e.nodeName)
                },
                input: function(e) {
                    return J.test(e.nodeName)
                },
                button: function(e) {
                    var t = e.nodeName.toLowerCase();
                    return "input" === t && "button" === e.type || "button" === t
                },
                text: function(e) {
                    var t;
                    return "input" === e.nodeName.toLowerCase() && "text" === e.type && (null == (t = e.getAttribute("type")) || "text" === t.toLowerCase())
                },
                first: ct(function() {
                    return [0]
                }),
                last: ct(function(e, t) {
                    return [t - 1]
                }),
                eq: ct(function(e, t, n) {
                    return [0 > n ? n + t : n]
                }),
                even: ct(function(e, t) {
                    for (var n = 0; t > n; n += 2)
                        e.push(n);
                    return e
                }),
                odd: ct(function(e, t) {
                    for (var n = 1; t > n; n += 2)
                        e.push(n);
                    return e
                }),
                lt: ct(function(e, t, n) {
                    for (var r = 0 > n ? n + t : n; --r >= 0;)
                        e.push(r);
                    return e
                }),
                gt: ct(function(e, t, n) {
                    for (var r = 0 > n ? n + t : n; ++r < t;)
                        e.push(r);
                    return e
                })
            }
        }, r.pseudos.nth = r.pseudos.eq;
        for (t in {
            radio: !0,
            checkbox: !0,
            file: !0,
            password: !0,
            image: !0
        })
            r.pseudos[t] = ft(t);
        for (t in {
            submit: !0,
            reset: !0
        })
            r.pseudos[t] = lt(t);
        return pt.prototype = r.filters = r.pseudos, r.setFilters = new pt, o = rt.compile = function(e, t) {
            var n,
                r = [],
                i = [],
                s = T[e + " "];
            if (!s) {
                t || (t = dt(e)), n = t.length;
                while (n--)
                    s = wt(t[n]), s[y] ? r.push(s) : i.push(s);
                s = T(e, Et(i, r))
            }
            return s
        }, n.sortStable = y.split("").sort(N).join("") === y, n.detectDuplicates = !!f, l(), n.sortDetached = ot(function(e) {
            return 1 & e.compareDocumentPosition(c.createElement("div"))
        }), ot(function(e) {
            return e.innerHTML = "<a href='#'></a>", "#" === e.firstChild.getAttribute("href")
        }) || ut("type|href|height|width", function(e, t, n) {
            return n ? void 0 : e.getAttribute(t, "type" === t.toLowerCase() ? 1 : 2)
        }), n.attributes && ot(function(e) {
            return e.innerHTML = "<input/>", e.firstChild.setAttribute("value", ""), "" === e.firstChild.getAttribute("value")
        }) || ut("value", function(e, t, n) {
            return n || "input" !== e.nodeName.toLowerCase() ? void 0 : e.defaultValue
        }), ot(function(e) {
            return null == e.getAttribute("disabled")
        }) || ut(H, function(e, t, n) {
            var r;
            return n ? void 0 : e[t] === !0 ? t.toLowerCase() : (r = e.getAttributeNode(t)) && r.specified ? r.value : null
        }), rt
    }(e);
    p.find = b, p.expr = b.selectors, p.expr[":"] = p.expr.pseudos, p.unique = b.uniqueSort, p.text = b.getText, p.isXMLDoc = b.isXML, p.contains = b.contains;
    var w = p.expr.match.needsContext,
        E = /^<(\w+)\s*\/?>(?:<\/\1>|)$/,
        S = /^.[^:#\[\.,]*$/;
    p.filter = function(e, t, n) {
        var r = t[0];
        return n && (e = ":not(" + e + ")"), 1 === t.length && 1 === r.nodeType ? p.find.matchesSelector(r, e) ? [r] : [] : p.find.matches(e, p.grep(t, function(e) {
            return 1 === e.nodeType
        }))
    }, p.fn.extend({
        find: function(e) {
            var t,
                n = [],
                r = this,
                i = r.length;
            if ("string" != typeof e)
                return this.pushStack(p(e).filter(function() {
                    for (t = 0; i > t; t++)
                        if (p.contains(r[t], this))
                            return !0
                }));
            for (t = 0; i > t; t++)
                p.find(e, r[t], n);
            return n = this.pushStack(i > 1 ? p.unique(n) : n), n.selector = this.selector ? this.selector + " " + e : e, n
        },
        filter: function(e) {
            return this.pushStack(x(this, e || [], !1))
        },
        not: function(e) {
            return this.pushStack(x(this, e || [], !0))
        },
        is: function(e) {
            return !!x(this, "string" == typeof e && w.test(e) ? p(e) : e || [], !1).length
        }
    });
    var T,
        N = e.document,
        C = /^(?:\s*(<[\w\W]+>)[^>]*|#([\w-]*))$/,
        k = p.fn.init = function(e, t) {
            var n,
                r;
            if (!e)
                return this;
            if ("string" == typeof e) {
                if (n = "<" === e.charAt(0) && ">" === e.charAt(e.length - 1) && e.length >= 3 ? [null, e, null] : C.exec(e), !n || !n[1] && t)
                    return !t || t.jquery ? (t || T).find(e) : this.constructor(t).find(e);
                if (n[1]) {
                    if (t = t instanceof p ? t[0] : t, p.merge(this, p.parseHTML(n[1], t && t.nodeType ? t.ownerDocument || t : N, !0)), E.test(n[1]) && p.isPlainObject(t))
                        for (n in t)
                            p.isFunction(this[n]) ? this[n](t[n]) : this.attr(n, t[n]);
                    return this
                }
                if (r = N.getElementById(n[2]), r && r.parentNode) {
                    if (r.id !== n[2])
                        return T.find(e);
                    this.length = 1, this[0] = r
                }
                return this.context = N, this.selector = e, this
            }
            return e.nodeType ? (this.context = this[0] = e, this.length = 1, this) : p.isFunction(e) ? "undefined" != typeof T.ready ? T.ready(e) : e(p) : (void 0 !== e.selector && (this.selector = e.selector, this.context = e.context), p.makeArray(e, this))
        };
    k.prototype = p.fn, T = p(N);
    var L = /^(?:parents|prev(?:Until|All))/,
        A = {
            children: !0,
            contents: !0,
            next: !0,
            prev: !0
        };
    p.extend({
        dir: function(e, t, n) {
            var r = [],
                i = e[t];
            while (i && 9 !== i.nodeType && (void 0 === n || 1 !== i.nodeType || !p(i).is(n)))
                1 === i.nodeType && r.push(i), i = i[t];
            return r
        },
        sibling: function(e, t) {
            for (var n = []; e; e = e.nextSibling)
                1 === e.nodeType && e !== t && n.push(e);
            return n
        }
    }), p.fn.extend({
        has: function(e) {
            var t,
                n = p(e, this),
                r = n.length;
            return this.filter(function() {
                for (t = 0; r > t; t++)
                    if (p.contains(this, n[t]))
                        return !0
            })
        },
        closest: function(e, t) {
            for (var n, r = 0, i = this.length, s = [], o = w.test(e) || "string" != typeof e ? p(e, t || this.context) : 0; i > r; r++)
                for (n = this[r]; n && n !== t; n = n.parentNode)
                    if (n.nodeType < 11 && (o ? o.index(n) > -1 : 1 === n.nodeType && p.find.matchesSelector(n, e))) {
                        s.push(n);
                        break
                    }
            return this.pushStack(s.length > 1 ? p.unique(s) : s)
        },
        index: function(e) {
            return e ? "string" == typeof e ? p.inArray(this[0], p(e)) : p.inArray(e.jquery ? e[0] : e, this) : this[0] && this[0].parentNode ? this.first().prevAll().length : -1
        },
        add: function(e, t) {
            return this.pushStack(p.unique(p.merge(this.get(), p(e, t))))
        },
        addBack: function(e) {
            return this.add(null == e ? this.prevObject : this.prevObject.filter(e))
        }
    }), p.each({
        parent: function(e) {
            var t = e.parentNode;
            return t && 11 !== t.nodeType ? t : null
        },
        parents: function(e) {
            return p.dir(e, "parentNode")
        },
        parentsUntil: function(e, t, n) {
            return p.dir(e, "parentNode", n)
        },
        next: function(e) {
            return O(e, "nextSibling")
        },
        prev: function(e) {
            return O(e, "previousSibling")
        },
        nextAll: function(e) {
            return p.dir(e, "nextSibling")
        },
        prevAll: function(e) {
            return p.dir(e, "previousSibling")
        },
        nextUntil: function(e, t, n) {
            return p.dir(e, "nextSibling", n)
        },
        prevUntil: function(e, t, n) {
            return p.dir(e, "previousSibling", n)
        },
        siblings: function(e) {
            return p.sibling((e.parentNode || {}).firstChild, e)
        },
        children: function(e) {
            return p.sibling(e.firstChild)
        },
        contents: function(e) {
            return p.nodeName(e, "iframe") ? e.contentDocument || e.contentWindow.document : p.merge([], e.childNodes)
        }
    }, function(e, t) {
        p.fn[e] = function(n, r) {
            var i = p.map(this, t, n);
            return "Until" !== e.slice(-5) && (r = n), r && "string" == typeof r && (i = p.filter(r, i)), this.length > 1 && (A[e] || (i = p.unique(i)), L.test(e) && (i = i.reverse())), this.pushStack(i)
        }
    });
    var M = /\S+/g,
        _ = {};
    p.Callbacks = function(e) {
        e = "string" == typeof e ? _[e] || D(e) : p.extend({}, e);
        var t,
            n,
            r,
            i,
            s,
            o,
            u = [],
            a = !e.once && [],
            f = function(c) {
                for (n = e.memory && c, r = !0, s = o || 0, o = 0, i = u.length, t = !0; u && i > s; s++)
                    if (u[s].apply(c[0], c[1]) === !1 && e.stopOnFalse) {
                        n = !1;
                        break
                    }
                t = !1, u && (a ? a.length && f(a.shift()) : n ? u = [] : l.disable())
            },
            l = {
                add: function() {
                    if (u) {
                        var r = u.length;
                        !function s(t) {
                            p.each(t, function(t, n) {
                                var r = p.type(n);
                                "function" === r ? e.unique && l.has(n) || u.push(n) : n && n.length && "string" !== r && s(n)
                            })
                        }(arguments), t ? i = u.length : n && (o = r, f(n))
                    }
                    return this
                },
                remove: function() {
                    return u && p.each(arguments, function(e, n) {
                        var r;
                        while ((r = p.inArray(n, u, r)) > -1)
                            u.splice(r, 1), t && (i >= r && i--, s >= r && s--)
                    }), this
                },
                has: function(e) {
                    return e ? p.inArray(e, u) > -1 : !!u && !!u.length
                },
                empty: function() {
                    return u = [], i = 0, this
                },
                disable: function() {
                    return u = a = n = void 0, this
                },
                disabled: function() {
                    return !u
                },
                lock: function() {
                    return a = void 0, n || l.disable(), this
                },
                locked: function() {
                    return !a
                },
                fireWith: function(e, n) {
                    return !u || r && !a || (n = n || [], n = [e, n.slice ? n.slice() : n], t ? a.push(n) : f(n)), this
                },
                fire: function() {
                    return l.fireWith(this, arguments), this
                },
                fired: function() {
                    return !!r
                }
            };
        return l
    }, p.extend({
        Deferred: function(e) {
            var t = [["resolve", "done", p.Callbacks("once memory"), "resolved"], ["reject", "fail", p.Callbacks("once memory"), "rejected"], ["notify", "progress", p.Callbacks("memory")]],
                n = "pending",
                r = {
                    state: function() {
                        return n
                    },
                    always: function() {
                        return i.done(arguments).fail(arguments), this
                    },
                    then: function() {
                        var e = arguments;
                        return p.Deferred(function(n) {
                            p.each(t, function(t, s) {
                                var o = p.isFunction(e[t]) && e[t];
                                i[s[1]](function() {
                                    var e = o && o.apply(this, arguments);
                                    e && p.isFunction(e.promise) ? e.promise().done(n.resolve).fail(n.reject).progress(n.notify) : n[s[0] + "With"](this === r ? n.promise() : this, o ? [e] : arguments)
                                })
                            }), e = null
                        }).promise()
                    },
                    promise: function(e) {
                        return null != e ? p.extend(e, r) : r
                    }
                },
                i = {};
            return r.pipe = r.then, p.each(t, function(e, s) {
                var o = s[2],
                    u = s[3];
                r[s[1]] = o.add, u && o.add(function() {
                    n = u
                }, t[1 ^ e][2].disable, t[2][2].lock), i[s[0]] = function() {
                    return i[s[0] + "With"](this === i ? r : this, arguments), this
                }, i[s[0] + "With"] = o.fireWith
            }), r.promise(i), e && e.call(i, i), i
        },
        when: function(e) {
            var t = 0,
                n = r.call(arguments),
                i = n.length,
                s = 1 !== i || e && p.isFunction(e.promise) ? i : 0,
                o = 1 === s ? e : p.Deferred(),
                u = function(e, t, n) {
                    return function(i) {
                        t[e] = this, n[e] = arguments.length > 1 ? r.call(arguments) : i, n === a ? o.notifyWith(t, n) : --s || o.resolveWith(t, n)
                    }
                },
                a,
                f,
                l;
            if (i > 1)
                for (a = new Array(i), f = new Array(i), l = new Array(i); i > t; t++)
                    n[t] && p.isFunction(n[t].promise) ? n[t].promise().done(u(t, l, n)).fail(o.reject).progress(u(t, f, a)) : --s;
            return s || o.resolveWith(l, n), o.promise()
        }
    });
    var P;
    p.fn.ready = function(e) {
        return p.ready.promise().done(e), this
    }, p.extend({
        isReady: !1,
        readyWait: 1,
        holdReady: function(e) {
            e ? p.readyWait++ : p.ready(!0)
        },
        ready: function(e) {
            if (e === !0 ? !--p.readyWait : !p.isReady) {
                if (!N.body)
                    return setTimeout(p.ready);
                p.isReady = !0, e !== !0 && --p.readyWait > 0 || (P.resolveWith(N, [p]), p.fn.trigger && p(N).trigger("ready").off("ready"))
            }
        }
    }), p.ready.promise = function(t) {
        if (!P)
            if (P = p.Deferred(), "complete" === N.readyState)
                setTimeout(p.ready);
            else if (N.addEventListener)
                N.addEventListener("DOMContentLoaded", B, !1), e.addEventListener("load", B, !1);
            else {
                N.attachEvent("onreadystatechange", B), e.attachEvent("onload", B);
                var n = !1;
                try {
                    n = null == e.frameElement && N.documentElement
                } catch (r) {}
                n && n.doScroll && !function i() {
                    if (!p.isReady) {
                        try {
                            n.doScroll("left")
                        } catch (e) {
                            return setTimeout(i, 50)
                        }
                        H(), p.ready()
                    }
                }()
            }
        return P.promise(t)
    };
    var j = "undefined",
        F;
    for (F in p(c))
        break;
    c.ownLast = "0" !== F, c.inlineBlockNeedsLayout = !1, p(function() {
        var e,
            t,
            n = N.getElementsByTagName("body")[0];
        n && (e = N.createElement("div"), e.style.cssText = "border:0;width:0;height:0;position:absolute;top:0;left:-9999px;margin-top:1px", t = N.createElement("div"), n.appendChild(e).appendChild(t), typeof t.style.zoom !== j && (t.style.cssText = "border:0;margin:0;width:1px;padding:1px;display:inline;zoom:1", (c.inlineBlockNeedsLayout = 3 === t.offsetWidth) && (n.style.zoom = 1)), n.removeChild(e), e = t = null)
    }), function() {
        var e = N.createElement("div");
        if (null == c.deleteExpando) {
            c.deleteExpando = !0;
            try {
                delete e.test
            } catch (t) {
                c.deleteExpando = !1
            }
        }
        e = null
    }(), p.acceptData = function(e) {
        var t = p.noData[(e.nodeName + " ").toLowerCase()],
            n = +e.nodeType || 1;
        return 1 !== n && 9 !== n ? !1 : !t || t !== !0 && e.getAttribute("classid") === t
    };
    var I = /^(?:\{[\w\W]*\}|\[[\w\W]*\])$/,
        q = /([A-Z])/g;
    p.extend({
        cache: {},
        noData: {
            "applet ": !0,
            "embed ": !0,
            "object ": "clsid:D27CDB6E-AE6D-11cf-96B8-444553540000"
        },
        hasData: function(e) {
            return e = e.nodeType ? p.cache[e[p.expando]] : e[p.expando], !!e && !U(e)
        },
        data: function(e, t, n) {
            return z(e, t, n)
        },
        removeData: function(e, t) {
            return W(e, t)
        },
        _data: function(e, t, n) {
            return z(e, t, n, !0)
        },
        _removeData: function(e, t) {
            return W(e, t, !0)
        }
    }), p.fn.extend({
        data: function(e, t) {
            var n,
                r,
                i,
                s = this[0],
                o = s && s.attributes;
            if (void 0 === e) {
                if (this.length && (i = p.data(s), 1 === s.nodeType && !p._data(s, "parsedAttrs"))) {
                    n = o.length;
                    while (n--)
                        r = o[n].name, 0 === r.indexOf("data-") && (r = p.camelCase(r.slice(5)), R(s, r, i[r]));
                    p._data(s, "parsedAttrs", !0)
                }
                return i
            }
            return "object" == typeof e ? this.each(function() {
                p.data(this, e)
            }) : arguments.length > 1 ? this.each(function() {
                p.data(this, e, t)
            }) : s ? R(s, e, p.data(s, e)) : void 0
        },
        removeData: function(e) {
            return this.each(function() {
                p.removeData(this, e)
            })
        }
    }), p.extend({
        queue: function(e, t, n) {
            var r;
            return e ? (t = (t || "fx") + "queue", r = p._data(e, t), n && (!r || p.isArray(n) ? r = p._data(e, t, p.makeArray(n)) : r.push(n)), r || []) : void 0
        },
        dequeue: function(e, t) {
            t = t || "fx";
            var n = p.queue(e, t),
                r = n.length,
                i = n.shift(),
                s = p._queueHooks(e, t),
                o = function() {
                    p.dequeue(e, t)
                };
            "inprogress" === i && (i = n.shift(), r--), i && ("fx" === t && n.unshift("inprogress"), delete s.stop, i.call(e, o, s)), !r && s && s.empty.fire()
        },
        _queueHooks: function(e, t) {
            var n = t + "queueHooks";
            return p._data(e, n) || p._data(e, n, {
                    empty: p.Callbacks("once memory").add(function() {
                        p._removeData(e, t + "queue"), p._removeData(e, n)
                    })
                })
        }
    }), p.fn.extend({
        queue: function(e, t) {
            var n = 2;
            return "string" != typeof e && (t = e, e = "fx", n--), arguments.length < n ? p.queue(this[0], e) : void 0 === t ? this : this.each(function() {
                var n = p.queue(this, e, t);
                p._queueHooks(this, e), "fx" === e && "inprogress" !== n[0] && p.dequeue(this, e)
            })
        },
        dequeue: function(e) {
            return this.each(function() {
                p.dequeue(this, e)
            })
        },
        clearQueue: function(e) {
            return this.queue(e || "fx", [])
        },
        promise: function(e, t) {
            var n,
                r = 1,
                i = p.Deferred(),
                s = this,
                o = this.length,
                u = function() {
                    --r || i.resolveWith(s, [s])
                };
            "string" != typeof e && (t = e, e = void 0), e = e || "fx";
            while (o--)
                n = p._data(s[o], e + "queueHooks"), n && n.empty && (r++, n.empty.add(u));
            return u(), i.promise(t)
        }
    });
    var X = /[+-]?(?:\d*\.|)\d+(?:[eE][+-]?\d+|)/.source,
        V = ["Top", "Right", "Bottom", "Left"],
        $ = function(e, t) {
            return e = t || e, "none" === p.css(e, "display") || !p.contains(e.ownerDocument, e)
        },
        J = p.access = function(e, t, n, r, i, s, o) {
            var u = 0,
                a = e.length,
                f = null == n;
            if ("object" === p.type(n)) {
                i = !0;
                for (u in n)
                    p.access(e, t, u, n[u], !0, s, o)
            } else if (void 0 !== r && (i = !0, p.isFunction(r) || (o = !0), f && (o ? (t.call(e, r), t = null) : (f = t, t = function(e, t, n) {
                return f.call(p(e), n)
            })), t))
                for (; a > u; u++)
                    t(e[u], n, o ? r : r.call(e[u], u, t(e[u], n)));
            return i ? e : f ? t.call(e) : a ? t(e[0], n) : s
        },
        K = /^(?:checkbox|radio)$/i;
    !function() {
        var e = N.createDocumentFragment(),
            t = N.createElement("div"),
            n = N.createElement("input");
        if (t.setAttribute("className", "t"), t.innerHTML = "  <link/><table></table><a href='/a'>a</a>", c.leadingWhitespace = 3 === t.firstChild.nodeType, c.tbody = !t.getElementsByTagName("tbody").length, c.htmlSerialize = !!t.getElementsByTagName("link").length, c.html5Clone = "<:nav></:nav>" !== N.createElement("nav").cloneNode(!0).outerHTML, n.type = "checkbox", n.checked = !0, e.appendChild(n), c.appendChecked = n.checked, t.innerHTML = "<textarea>x</textarea>", c.noCloneChecked = !!t.cloneNode(!0).lastChild.defaultValue, e.appendChild(t), t.innerHTML = "<input type='radio' checked='checked' name='t'/>", c.checkClone = t.cloneNode(!0).cloneNode(!0).lastChild.checked, c.noCloneEvent = !0, t.attachEvent && (t.attachEvent("onclick", function() {
            c.noCloneEvent = !1
        }), t.cloneNode(!0).click()), null == c.deleteExpando) {
            c.deleteExpando = !0;
            try {
                delete t.test
            } catch (r) {
                c.deleteExpando = !1
            }
        }
        e = t = n = null
    }(), function() {
        var t,
            n,
            r = N.createElement("div");
        for (t in {
            submit: !0,
            change: !0,
            focusin: !0
        })
            n = "on" + t, (c[t + "Bubbles"] = n in e) || (r.setAttribute(n, "t"), c[t + "Bubbles"] = r.attributes[n].expando === !1);
        r = null
    }();
    var Q = /^(?:input|select|textarea)$/i,
        G = /^key/,
        Y = /^(?:mouse|contextmenu)|click/,
        Z = /^(?:focusinfocus|focusoutblur)$/,
        et = /^([^.]*)(?:\.(.+)|)$/;
    p.event = {
        global: {},
        add: function(e, t, n, r, i) {
            var s,
                o,
                u,
                a,
                f,
                l,
                c,
                h,
                d,
                v,
                m,
                g = p._data(e);
            if (g) {
                n.handler && (a = n, n = a.handler, i = a.selector), n.guid || (n.guid = p.guid++), (o = g.events) || (o = g.events = {}), (l = g.handle) || (l = g.handle = function(e) {
                    return typeof p === j || e && p.event.triggered === e.type ? void 0 : p.event.dispatch.apply(l.elem, arguments)
                }, l.elem = e), t = (t || "").match(M) || [""], u = t.length;
                while (u--)
                    s = et.exec(t[u]) || [], d = m = s[1], v = (s[2] || "").split(".").sort(), d && (f = p.event.special[d] || {}, d = (i ? f.delegateType : f.bindType) || d, f = p.event.special[d] || {}, c = p.extend({
                        type: d,
                        origType: m,
                        data: r,
                        handler: n,
                        guid: n.guid,
                        selector: i,
                        needsContext: i && p.expr.match.needsContext.test(i),
                        namespace: v.join(".")
                    }, a), (h = o[d]) || (h = o[d] = [], h.delegateCount = 0, f.setup && f.setup.call(e, r, v, l) !== !1 || (e.addEventListener ? e.addEventListener(d, l, !1) : e.attachEvent && e.attachEvent("on" + d, l))), f.add && (f.add.call(e, c), c.handler.guid || (c.handler.guid = n.guid)), i ? h.splice(h.delegateCount++, 0, c) : h.push(c), p.event.global[d] = !0);
                e = null
            }
        },
        remove: function(e, t, n, r, i) {
            var s,
                o,
                u,
                a,
                f,
                l,
                c,
                h,
                d,
                v,
                m,
                g = p.hasData(e) && p._data(e);
            if (g && (l = g.events)) {
                t = (t || "").match(M) || [""], f = t.length;
                while (f--)
                    if (u = et.exec(t[f]) || [], d = m = u[1], v = (u[2] || "").split(".").sort(), d) {
                        c = p.event.special[d] || {}, d = (r ? c.delegateType : c.bindType) || d, h = l[d] || [], u = u[2] && new RegExp("(^|\\.)" + v.join("\\.(?:.*\\.|)") + "(\\.|$)"), a = s = h.length;
                        while (s--)
                            o = h[s], !i && m !== o.origType || n && n.guid !== o.guid || u && !u.test(o.namespace) || r && r !== o.selector && ("**" !== r || !o.selector) || (h.splice(s, 1), o.selector && h.delegateCount--, c.remove && c.remove.call(e, o));
                        a && !h.length && (c.teardown && c.teardown.call(e, v, g.handle) !== !1 || p.removeEvent(e, d, g.handle), delete l[d])
                    } else
                        for (d in l)
                            p.event.remove(e, d + t[f], n, r, !0);
                p.isEmptyObject(l) && (delete g.handle, p._removeData(e, "events"))
            }
        },
        trigger: function(t, n, r, i) {
            var s,
                o,
                u,
                a,
                l,
                c,
                h,
                d = [r || N],
                v = f.call(t, "type") ? t.type : t,
                m = f.call(t, "namespace") ? t.namespace.split(".") : [];
            if (u = c = r = r || N, 3 !== r.nodeType && 8 !== r.nodeType && !Z.test(v + p.event.triggered) && (v.indexOf(".") >= 0 && (m = v.split("."), v = m.shift(), m.sort()), o = v.indexOf(":") < 0 && "on" + v, t = t[p.expando] ? t : new p.Event(v, "object" == typeof t && t), t.isTrigger = i ? 2 : 3, t.namespace = m.join("."), t.namespace_re = t.namespace ? new RegExp("(^|\\.)" + m.join("\\.(?:.*\\.|)") + "(\\.|$)") : null, t.result = void 0, t.target || (t.target = r), n = null == n ? [t] : p.makeArray(n, [t]), l = p.event.special[v] || {}, i || !l.trigger || l.trigger.apply(r, n) !== !1)) {
                if (!i && !l.noBubble && !p.isWindow(r)) {
                    for (a = l.delegateType || v, Z.test(a + v) || (u = u.parentNode); u; u = u.parentNode)
                        d.push(u), c = u;
                    c === (r.ownerDocument || N) && d.push(c.defaultView || c.parentWindow || e)
                }
                h = 0;
                while ((u = d[h++]) && !t.isPropagationStopped())
                    t.type = h > 1 ? a : l.bindType || v, s = (p._data(u, "events") || {})[t.type] && p._data(u, "handle"), s && s.apply(u, n), s = o && u[o], s && s.apply && p.acceptData(u) && (t.result = s.apply(u, n), t.result === !1 && t.preventDefault());
                if (t.type = v, !i && !t.isDefaultPrevented() && (!l._default || l._default.apply(d.pop(), n) === !1) && p.acceptData(r) && o && r[v] && !p.isWindow(r)) {
                    c = r[o], c && (r[o] = null), p.event.triggered = v;
                    try {
                        r[v]()
                    } catch (g) {}
                    p.event.triggered = void 0, c && (r[o] = c)
                }
                return t.result
            }
        },
        dispatch: function(e) {
            e = p.event.fix(e);
            var t,
                n,
                i,
                s,
                o,
                u = [],
                a = r.call(arguments),
                f = (p._data(this, "events") || {})[e.type] || [],
                l = p.event.special[e.type] || {};
            if (a[0] = e, e.delegateTarget = this, !l.preDispatch || l.preDispatch.call(this, e) !== !1) {
                u = p.event.handlers.call(this, e, f), t = 0;
                while ((s = u[t++]) && !e.isPropagationStopped()) {
                    e.currentTarget = s.elem, o = 0;
                    while ((i = s.handlers[o++]) && !e.isImmediatePropagationStopped())
                        (!e.namespace_re || e.namespace_re.test(i.namespace)) && (e.handleObj = i, e.data = i.data, n = ((p.event.special[i.origType] || {}).handle || i.handler).apply(s.elem, a), void 0 !== n && (e.result = n) === !1 && (e.preventDefault(), e.stopPropagation()))
                }
                return l.postDispatch && l.postDispatch.call(this, e), e.result
            }
        },
        handlers: function(e, t) {
            var n,
                r,
                i,
                s,
                o = [],
                u = t.delegateCount,
                a = e.target;
            if (u && a.nodeType && (!e.button || "click" !== e.type))
                for (; a != this; a = a.parentNode || this)
                    if (1 === a.nodeType && (a.disabled !== !0 || "click" !== e.type)) {
                        for (i = [], s = 0; u > s; s++)
                            r = t[s], n = r.selector + " ", void 0 === i[n] && (i[n] = r.needsContext ? p(n, this).index(a) >= 0 : p.find(n, this, null, [a]).length), i[n] && i.push(r);
                        i.length && o.push({
                            elem: a,
                            handlers: i
                        })
                    }
            return u < t.length && o.push({
                elem: this,
                handlers: t.slice(u)
            }), o
        },
        fix: function(e) {
            if (e[p.expando])
                return e;
            var t,
                n,
                r,
                i = e.type,
                s = e,
                o = this.fixHooks[i];
            o || (this.fixHooks[i] = o = Y.test(i) ? this.mouseHooks : G.test(i) ? this.keyHooks : {}), r = o.props ? this.props.concat(o.props) : this.props, e = new p.Event(s), t = r.length;
            while (t--)
                n = r[t], e[n] = s[n];
            return e.target || (e.target = s.srcElement || N), 3 === e.target.nodeType && (e.target = e.target.parentNode), e.metaKey = !!e.metaKey, o.filter ? o.filter(e, s) : e
        },
        props: "altKey bubbles cancelable ctrlKey currentTarget eventPhase metaKey relatedTarget shiftKey target timeStamp view which".split(" "),
        fixHooks: {},
        keyHooks: {
            props: "char charCode key keyCode".split(" "),
            filter: function(e, t) {
                return null == e.which && (e.which = null != t.charCode ? t.charCode : t.keyCode), e
            }
        },
        mouseHooks: {
            props: "button buttons clientX clientY fromElement offsetX offsetY pageX pageY screenX screenY toElement".split(" "),
            filter: function(e, t) {
                var n,
                    r,
                    i,
                    s = t.button,
                    o = t.fromElement;
                return null == e.pageX && null != t.clientX && (r = e.target.ownerDocument || N, i = r.documentElement, n = r.body, e.pageX = t.clientX + (i && i.scrollLeft || n && n.scrollLeft || 0) - (i && i.clientLeft || n && n.clientLeft || 0), e.pageY = t.clientY + (i && i.scrollTop || n && n.scrollTop || 0) - (i && i.clientTop || n && n.clientTop || 0)), !e.relatedTarget && o && (e.relatedTarget = o === e.target ? t.toElement : o), e.which || void 0 === s || (e.which = 1 & s ? 1 : 2 & s ? 3 : 4 & s ? 2 : 0), e
            }
        },
        special: {
            load: {
                noBubble: !0
            },
            focus: {
                trigger: function() {
                    if (this !== rt() && this.focus)
                        try {
                            return this.focus(), !1
                        } catch (e) {}
                },
                delegateType: "focusin"
            },
            blur: {
                trigger: function() {
                    return this === rt() && this.blur ? (this.blur(), !1) : void 0
                },
                delegateType: "focusout"
            },
            click: {
                trigger: function() {
                    return p.nodeName(this, "input") && "checkbox" === this.type && this.click ? (this.click(), !1) : void 0
                },
                _default: function(e) {
                    return p.nodeName(e.target, "a")
                }
            },
            beforeunload: {
                postDispatch: function(e) {
                    void 0 !== e.result && (e.originalEvent.returnValue = e.result)
                }
            }
        },
        simulate: function(e, t, n, r) {
            var i = p.extend(new p.Event, n, {
                type: e,
                isSimulated: !0,
                originalEvent: {}
            });
            r ? p.event.trigger(i, null, t) : p.event.dispatch.call(t, i), i.isDefaultPrevented() && n.preventDefault()
        }
    }, p.removeEvent = N.removeEventListener ? function(e, t, n) {
        e.removeEventListener && e.removeEventListener(t, n, !1)
    } : function(e, t, n) {
        var r = "on" + t;
        e.detachEvent && (typeof e[r] === j && (e[r] = null), e.detachEvent(r, n))
    }, p.Event = function(e, t) {
        return this instanceof p.Event ? (e && e.type ? (this.originalEvent = e, this.type = e.type, this.isDefaultPrevented = e.defaultPrevented || void 0 === e.defaultPrevented && (e.returnValue === !1 || e.getPreventDefault && e.getPreventDefault()) ? tt : nt) : this.type = e, t && p.extend(this, t), this.timeStamp = e && e.timeStamp || p.now(), void (this[p.expando] = !0)) : new p.Event(e, t)
    }, p.Event.prototype = {
        isDefaultPrevented: nt,
        isPropagationStopped: nt,
        isImmediatePropagationStopped: nt,
        preventDefault: function() {
            var e = this.originalEvent;
            this.isDefaultPrevented = tt, e && (e.preventDefault ? e.preventDefault() : e.returnValue = !1)
        },
        stopPropagation: function() {
            var e = this.originalEvent;
            this.isPropagationStopped = tt, e && (e.stopPropagation && e.stopPropagation(), e.cancelBubble = !0)
        },
        stopImmediatePropagation: function() {
            this.isImmediatePropagationStopped = tt, this.stopPropagation()
        }
    }, p.each({
        mouseenter: "mouseover",
        mouseleave: "mouseout"
    }, function(e, t) {
        p.event.special[e] = {
            delegateType: t,
            bindType: t,
            handle: function(e) {
                var n,
                    r = this,
                    i = e.relatedTarget,
                    s = e.handleObj;
                return (!i || i !== r && !p.contains(r, i)) && (e.type = s.origType, n = s.handler.apply(this, arguments), e.type = t), n
            }
        }
    }), c.submitBubbles || (p.event.special.submit = {
        setup: function() {
            return p.nodeName(this, "form") ? !1 : void p.event.add(this, "click._submit keypress._submit", function(e) {
                var t = e.target,
                    n = p.nodeName(t, "input") || p.nodeName(t, "button") ? t.form : void 0;
                n && !p._data(n, "submitBubbles") && (p.event.add(n, "submit._submit", function(e) {
                    e._submit_bubble = !0
                }), p._data(n, "submitBubbles", !0))
            })
        },
        postDispatch: function(e) {
            e._submit_bubble && (delete e._submit_bubble, this.parentNode && !e.isTrigger && p.event.simulate("submit", this.parentNode, e, !0))
        },
        teardown: function() {
            return p.nodeName(this, "form") ? !1 : void p.event.remove(this, "._submit")
        }
    }), c.changeBubbles || (p.event.special.change = {
        setup: function() {
            return Q.test(this.nodeName) ? (("checkbox" === this.type || "radio" === this.type) && (p.event.add(this, "propertychange._change", function(e) {
                "checked" === e.originalEvent.propertyName && (this._just_changed = !0)
            }), p.event.add(this, "click._change", function(e) {
                this._just_changed && !e.isTrigger && (this._just_changed = !1), p.event.simulate("change", this, e, !0)
            })), !1) : void p.event.add(this, "beforeactivate._change", function(e) {
                var t = e.target;
                Q.test(t.nodeName) && !p._data(t, "changeBubbles") && (p.event.add(t, "change._change", function(e) {
                    !this.parentNode || e.isSimulated || e.isTrigger || p.event.simulate("change", this.parentNode, e, !0)
                }), p._data(t, "changeBubbles", !0))
            })
        },
        handle: function(e) {
            var t = e.target;
            return this !== t || e.isSimulated || e.isTrigger || "radio" !== t.type && "checkbox" !== t.type ? e.handleObj.handler.apply(this, arguments) : void 0
        },
        teardown: function() {
            return p.event.remove(this, "._change"), !Q.test(this.nodeName)
        }
    }), c.focusinBubbles || p.each({
        focus: "focusin",
        blur: "focusout"
    }, function(e, t) {
        var n = function(e) {
            p.event.simulate(t, e.target, p.event.fix(e), !0)
        };
        p.event.special[t] = {
            setup: function() {
                var r = this.ownerDocument || this,
                    i = p._data(r, t);
                i || r.addEventListener(e, n, !0), p._data(r, t, (i || 0) + 1)
            },
            teardown: function() {
                var r = this.ownerDocument || this,
                    i = p._data(r, t) - 1;
                i ? p._data(r, t, i) : (r.removeEventListener(e, n, !0), p._removeData(r, t))
            }
        }
    }), p.fn.extend({
        on: function(e, t, n, r, i) {
            var s,
                o;
            if ("object" == typeof e) {
                "string" != typeof t && (n = n || t, t = void 0);
                for (s in e)
                    this.on(s, t, n, e[s], i);
                return this
            }
            if (null == n && null == r ? (r = t, n = t = void 0) : null == r && ("string" == typeof t ? (r = n, n = void 0) : (r = n, n = t, t = void 0)), r === !1)
                r = nt;
            else if (!r)
                return this;
            return 1 === i && (o = r, r = function(e) {
                return p().off(e), o.apply(this, arguments)
            }, r.guid = o.guid || (o.guid = p.guid++)), this.each(function() {
                p.event.add(this, e, r, n, t)
            })
        },
        one: function(e, t, n, r) {
            return this.on(e, t, n, r, 1)
        },
        off: function(e, t, n) {
            var r,
                i;
            if (e && e.preventDefault && e.handleObj)
                return r = e.handleObj, p(e.delegateTarget).off(r.namespace ? r.origType + "." + r.namespace : r.origType, r.selector, r.handler), this;
            if ("object" == typeof e) {
                for (i in e)
                    this.off(i, t, e[i]);
                return this
            }
            return (t === !1 || "function" == typeof t) && (n = t, t = void 0), n === !1 && (n = nt), this.each(function() {
                p.event.remove(this, e, n, t)
            })
        },
        trigger: function(e, t) {
            return this.each(function() {
                p.event.trigger(e, t, this)
            })
        },
        triggerHandler: function(e, t) {
            var n = this[0];
            return n ? p.event.trigger(e, t, n, !0) : void 0
        }
    });
    var st = "abbr|article|aside|audio|bdi|canvas|data|datalist|details|figcaption|figure|footer|header|hgroup|mark|meter|nav|output|progress|section|summary|time|video",
        ot = / jQuery\d+="(?:null|\d+)"/g,
        ut = new RegExp("<(?:" + st + ")[\\s/>]", "i"),
        at = /^\s+/,
        ft = /<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/gi,
        lt = /<([\w:]+)/,
        ct = /<tbody/i,
        ht = /<|&#?\w+;/,
        pt = /<(?:script|style|link)/i,
        dt = /checked\s*(?:[^=]|=\s*.checked.)/i,
        vt = /^$|\/(?:java|ecma)script/i,
        mt = /^true\/(.*)/,
        gt = /^\s*<!(?:\[CDATA\[|--)|(?:\]\]|--)>\s*$/g,
        yt = {
            option: [1, "<select multiple='multiple'>", "</select>"],
            legend: [1, "<fieldset>", "</fieldset>"],
            area: [1, "<map>", "</map>"],
            param: [1, "<object>", "</object>"],
            thead: [1, "<table>", "</table>"],
            tr: [2, "<table><tbody>", "</tbody></table>"],
            col: [2, "<table><tbody></tbody><colgroup>", "</colgroup></table>"],
            td: [3, "<table><tbody><tr>", "</tr></tbody></table>"],
            _default: c.htmlSerialize ? [0, "", ""] : [1, "X<div>", "</div>"]
        },
        bt = it(N),
        wt = bt.appendChild(N.createElement("div"));
    yt.optgroup = yt.option, yt.tbody = yt.tfoot = yt.colgroup = yt.caption = yt.thead, yt.th = yt.td, p.extend({
        clone: function(e, t, n) {
            var r,
                i,
                s,
                o,
                u,
                a = p.contains(e.ownerDocument, e);
            if (c.html5Clone || p.isXMLDoc(e) || !ut.test("<" + e.nodeName + ">") ? s = e.cloneNode(!0) : (wt.innerHTML = e.outerHTML, wt.removeChild(s = wt.firstChild)), !(c.noCloneEvent && c.noCloneChecked || 1 !== e.nodeType && 11 !== e.nodeType || p.isXMLDoc(e)))
                for (r = Et(s), u = Et(e), o = 0; null != (i = u[o]); ++o)
                    r[o] && Lt(i, r[o]);
            if (t)
                if (n)
                    for (u = u || Et(e), r = r || Et(s), o = 0; null != (i = u[o]); o++)
                        kt(i, r[o]);
                else
                    kt(e, s);
            return r = Et(s, "script"), r.length > 0 && Ct(r, !a && Et(e, "script")), r = u = i = null, s
        },
        buildFragment: function(e, t, n, r) {
            for (var i, s, o, u, a, f, l, h = e.length, d = it(t), v = [], m = 0; h > m; m++)
                if (s = e[m], s || 0 === s)
                    if ("object" === p.type(s))
                        p.merge(v, s.nodeType ? [s] : s);
                    else if (ht.test(s)) {
                        u = u || d.appendChild(t.createElement("div")), a = (lt.exec(s) || ["", ""])[1].toLowerCase(), l = yt[a] || yt._default, u.innerHTML = l[1] + s.replace(ft, "<$1></$2>") + l[2], i = l[0];
                        while (i--)
                            u = u.lastChild;
                        if (!c.leadingWhitespace && at.test(s) && v.push(t.createTextNode(at.exec(s)[0])), !c.tbody) {
                            s = "table" !== a || ct.test(s) ? "<table>" !== l[1] || ct.test(s) ? 0 : u : u.firstChild, i = s && s.childNodes.length;
                            while (i--)
                                p.nodeName(f = s.childNodes[i], "tbody") && !f.childNodes.length && s.removeChild(f)
                        }
                        p.merge(v, u.childNodes), u.textContent = "";
                        while (u.firstChild)
                            u.removeChild(u.firstChild);
                        u = d.lastChild
                    } else
                        v.push(t.createTextNode(s));
            u && d.removeChild(u), c.appendChecked || p.grep(Et(v, "input"), St), m = 0;
            while (s = v[m++])
                if ((!r || -1 === p.inArray(s, r)) && (o = p.contains(s.ownerDocument, s), u = Et(d.appendChild(s), "script"), o && Ct(u), n)) {
                    i = 0;
                    while (s = u[i++])
                        vt.test(s.type || "") && n.push(s)
                }
            return u = null, d
        },
        cleanData: function(e, t) {
            for (var r, i, s, o, u = 0, a = p.expando, f = p.cache, l = c.deleteExpando, h = p.event.special; null != (r = e[u]); u++)
                if ((t || p.acceptData(r)) && (s = r[a], o = s && f[s])) {
                    if (o.events)
                        for (i in o.events)
                            h[i] ? p.event.remove(r, i) : p.removeEvent(r, i, o.handle);
                    f[s] && (delete f[s], l ? delete r[a] : typeof r.removeAttribute !== j ? r.removeAttribute(a) : r[a] = null, n.push(s))
                }
        }
    }), p.fn.extend({
        text: function(e) {
            return J(this, function(e) {
                return void 0 === e ? p.text(this) : this.empty().append((this[0] && this[0].ownerDocument || N).createTextNode(e))
            }, null, e, arguments.length)
        },
        append: function() {
            return this.domManip(arguments, function(e) {
                if (1 === this.nodeType || 11 === this.nodeType || 9 === this.nodeType) {
                    var t = xt(this, e);
                    t.appendChild(e)
                }
            })
        },
        prepend: function() {
            return this.domManip(arguments, function(e) {
                if (1 === this.nodeType || 11 === this.nodeType || 9 === this.nodeType) {
                    var t = xt(this, e);
                    t.insertBefore(e, t.firstChild)
                }
            })
        },
        before: function() {
            return this.domManip(arguments, function(e) {
                this.parentNode && this.parentNode.insertBefore(e, this)
            })
        },
        after: function() {
            return this.domManip(arguments, function(e) {
                this.parentNode && this.parentNode.insertBefore(e, this.nextSibling)
            })
        },
        remove: function(e, t) {
            for (var n, r = e ? p.filter(e, this) : this, i = 0; null != (n = r[i]); i++)
                t || 1 !== n.nodeType || p.cleanData(Et(n)), n.parentNode && (t && p.contains(n.ownerDocument, n) && Ct(Et(n, "script")), n.parentNode.removeChild(n));
            return this
        },
        empty: function() {
            for (var e, t = 0; null != (e = this[t]); t++) {
                1 === e.nodeType && p.cleanData(Et(e, !1));
                while (e.firstChild)
                    e.removeChild(e.firstChild);
                e.options && p.nodeName(e, "select") && (e.options.length = 0)
            }
            return this
        },
        clone: function(e, t) {
            return e = null == e ? !1 : e, t = null == t ? e : t, this.map(function() {
                return p.clone(this, e, t)
            })
        },
        html: function(e) {
            return J(this, function(e) {
                var t = this[0] || {},
                    n = 0,
                    r = this.length;
                if (void 0 === e)
                    return 1 === t.nodeType ? t.innerHTML.replace(ot, "") : void 0;
                if (!("string" != typeof e || pt.test(e) || !c.htmlSerialize && ut.test(e) || !c.leadingWhitespace && at.test(e) || yt[(lt.exec(e) || ["", ""])[1].toLowerCase()])) {
                    e = e.replace(ft, "<$1></$2>");
                    try {
                        for (; r > n; n++)
                            t = this[n] || {}, 1 === t.nodeType && (p.cleanData(Et(t, !1)), t.innerHTML = e);
                        t = 0
                    } catch (i) {}
                }
                t && this.empty().append(e)
            }, null, e, arguments.length)
        },
        replaceWith: function() {
            var e = arguments[0];
            return this.domManip(arguments, function(t) {
                e = this.parentNode, p.cleanData(Et(this)), e && e.replaceChild(t, this)
            }), e && (e.length || e.nodeType) ? this : this.remove()
        },
        detach: function(e) {
            return this.remove(e, !0)
        },
        domManip: function(e, t) {
            e = i.apply([], e);
            var n,
                r,
                s,
                o,
                u,
                a,
                f = 0,
                l = this.length,
                h = this,
                d = l - 1,
                v = e[0],
                m = p.isFunction(v);
            if (m || l > 1 && "string" == typeof v && !c.checkClone && dt.test(v))
                return this.each(function(n) {
                    var r = h.eq(n);
                    m && (e[0] = v.call(this, n, r.html())), r.domManip(e, t)
                });
            if (l && (a = p.buildFragment(e, this[0].ownerDocument, !1, this), n = a.firstChild, 1 === a.childNodes.length && (a = n), n)) {
                for (o = p.map(Et(a, "script"), Tt), s = o.length; l > f; f++)
                    r = a, f !== d && (r = p.clone(r, !0, !0), s && p.merge(o, Et(r, "script"))), t.call(this[f], r, f);
                if (s)
                    for (u = o[o.length - 1].ownerDocument, p.map(o, Nt), f = 0; s > f; f++)
                        r = o[f], vt.test(r.type || "") && !p._data(r, "globalEval") && p.contains(u, r) && (r.src ? p._evalUrl && p._evalUrl(r.src) : p.globalEval((r.text || r.textContent || r.innerHTML || "").replace(gt, "")));
                a = n = null
            }
            return this
        }
    }), p.each({
        appendTo: "append",
        prependTo: "prepend",
        insertBefore: "before",
        insertAfter: "after",
        replaceAll: "replaceWith"
    }, function(e, t) {
        p.fn[e] = function(e) {
            for (var n, r = 0, i = [], o = p(e), u = o.length - 1; u >= r; r++)
                n = r === u ? this : this.clone(!0), p(o[r])[t](n), s.apply(i, n.get());
            return this.pushStack(i)
        }
    });
    var At,
        Ot = {};
    !function() {
        var e,
            t,
            n = N.createElement("div"),
            r = "-webkit-box-sizing:content-box;-moz-box-sizing:content-box;box-sizing:content-box;display:block;padding:0;margin:0;border:0";
        n.innerHTML = "  <link/><table></table><a href='/a'>a</a><input type='checkbox'/>", e = n.getElementsByTagName("a")[0], e.style.cssText = "float:left;opacity:.5", c.opacity = /^0.5/.test(e.style.opacity), c.cssFloat = !!e.style.cssFloat, n.style.backgroundClip = "content-box", n.cloneNode(!0).style.backgroundClip = "", c.clearCloneStyle = "content-box" === n.style.backgroundClip, e = n = null, c.shrinkWrapBlocks = function() {
            var e,
                n,
                i,
                s;
            if (null == t) {
                if (e = N.getElementsByTagName("body")[0], !e)
                    return;
                s = "border:0;width:0;height:0;position:absolute;top:0;left:-9999px", n = N.createElement("div"), i = N.createElement("div"), e.appendChild(n).appendChild(i), t = !1, typeof i.style.zoom !== j && (i.style.cssText = r + ";width:1px;padding:1px;zoom:1", i.innerHTML = "<div></div>", i.firstChild.style.width = "5px", t = 3 !== i.offsetWidth), e.removeChild(n), e = n = i = null
            }
            return t
        }
    }();
    var Dt = /^margin/,
        Pt = new RegExp("^(" + X + ")(?!px)[a-z%]+$", "i"),
        Ht,
        Bt,
        jt = /^(top|right|bottom|left)$/;
    e.getComputedStyle ? (Ht = function(e) {
        return e.ownerDocument.defaultView.getComputedStyle(e, null)
    }, Bt = function(e, t, n) {
        var r,
            i,
            s,
            o,
            u = e.style;
        return n = n || Ht(e), o = n ? n.getPropertyValue(t) || n[t] : void 0, n && ("" !== o || p.contains(e.ownerDocument, e) || (o = p.style(e, t)), Pt.test(o) && Dt.test(t) && (r = u.width, i = u.minWidth, s = u.maxWidth, u.minWidth = u.maxWidth = u.width = o, o = n.width, u.width = r, u.minWidth = i, u.maxWidth = s)), void 0 === o ? o : o + ""
    }) : N.documentElement.currentStyle && (Ht = function(e) {
        return e.currentStyle
    }, Bt = function(e, t, n) {
        var r,
            i,
            s,
            o,
            u = e.style;
        return n = n || Ht(e), o = n ? n[t] : void 0, null == o && u && u[t] && (o = u[t]), Pt.test(o) && !jt.test(t) && (r = u.left, i = e.runtimeStyle, s = i && i.left, s && (i.left = e.currentStyle.left), u.left = "fontSize" === t ? "1em" : o, o = u.pixelLeft + "px", u.left = r, s && (i.left = s)), void 0 === o ? o : o + "" || "auto"
    }), !function() {
        function l() {
            var t,
                n,
                u = N.getElementsByTagName("body")[0];
            u && (t = N.createElement("div"), n = N.createElement("div"), t.style.cssText = a, u.appendChild(t).appendChild(n), n.style.cssText = "-webkit-box-sizing:border-box;-moz-box-sizing:border-box;box-sizing:border-box;position:absolute;display:block;padding:1px;border:1px;width:4px;margin-top:1%;top:1%", p.swap(u, null != u.style.zoom ? {
                zoom: 1
            } : {}, function() {
                r = 4 === n.offsetWidth
            }), i = !0, s = !1, o = !0, e.getComputedStyle && (s = "1%" !== (e.getComputedStyle(n, null) || {}).top, i = "4px" === (e.getComputedStyle(n, null) || {
                width: "4px"
            }).width), u.removeChild(t), n = u = null)
        }
        var t,
            n,
            r,
            i,
            s,
            o,
            u = N.createElement("div"),
            a = "border:0;width:0;height:0;position:absolute;top:0;left:-9999px",
            f = "-webkit-box-sizing:content-box;-moz-box-sizing:content-box;box-sizing:content-box;display:block;padding:0;margin:0;border:0";
        u.innerHTML = "  <link/><table></table><a href='/a'>a</a><input type='checkbox'/>", t = u.getElementsByTagName("a")[0], t.style.cssText = "float:left;opacity:.5", c.opacity = /^0.5/.test(t.style.opacity), c.cssFloat = !!t.style.cssFloat, u.style.backgroundClip = "content-box", u.cloneNode(!0).style.backgroundClip = "", c.clearCloneStyle = "content-box" === u.style.backgroundClip, t = u = null, p.extend(c, {
            reliableHiddenOffsets: function() {
                if (null != n)
                    return n;
                var e,
                    t,
                    r,
                    i = N.createElement("div"),
                    s = N.getElementsByTagName("body")[0];
                if (s)
                    return i.setAttribute("className", "t"), i.innerHTML = "  <link/><table></table><a href='/a'>a</a><input type='checkbox'/>", e = N.createElement("div"), e.style.cssText = a, s.appendChild(e).appendChild(i), i.innerHTML = "<table><tr><td></td><td>t</td></tr></table>", t = i.getElementsByTagName("td"), t[0].style.cssText = "padding:0;margin:0;border:0;display:none", r = 0 === t[0].offsetHeight, t[0].style.display = "", t[1].style.display = "none", n = r && 0 === t[0].offsetHeight, s.removeChild(e), i = s = null, n
            },
            boxSizing: function() {
                return null == r && l(), r
            },
            boxSizingReliable: function() {
                return null == i && l(), i
            },
            pixelPosition: function() {
                return null == s && l(), s
            },
            reliableMarginRight: function() {
                var t,
                    n,
                    r,
                    i;
                if (null == o && e.getComputedStyle) {
                    if (t = N.getElementsByTagName("body")[0], !t)
                        return;
                    n = N.createElement("div"), r = N.createElement("div"), n.style.cssText = a, t.appendChild(n).appendChild(r), i = r.appendChild(N.createElement("div")), i.style.cssText = r.style.cssText = f, i.style.marginRight = i.style.width = "0", r.style.width = "1px", o = !parseFloat((e.getComputedStyle(i, null) || {}).marginRight), t.removeChild(n)
                }
                return o
            }
        })
    }(), p.swap = function(e, t, n, r) {
        var i,
            s,
            o = {};
        for (s in t)
            o[s] = e.style[s], e.style[s] = t[s];
        i = n.apply(e, r || []);
        for (s in t)
            e.style[s] = o[s];
        return i
    };
    var It = /alpha\([^)]*\)/i,
        qt = /opacity\s*=\s*([^)]*)/,
        Rt = /^(none|table(?!-c[ea]).+)/,
        Ut = new RegExp("^(" + X + ")(.*)$", "i"),
        zt = new RegExp("^([+-])=(" + X + ")", "i"),
        Wt = {
            position: "absolute",
            visibility: "hidden",
            display: "block"
        },
        Xt = {
            letterSpacing: 0,
            fontWeight: 400
        },
        Vt = ["Webkit", "O", "Moz", "ms"];
    p.extend({
        cssHooks: {
            opacity: {
                get: function(e, t) {
                    if (t) {
                        var n = Bt(e, "opacity");
                        return "" === n ? "1" : n
                    }
                }
            }
        },
        cssNumber: {
            columnCount: !0,
            fillOpacity: !0,
            fontWeight: !0,
            lineHeight: !0,
            opacity: !0,
            order: !0,
            orphans: !0,
            widows: !0,
            zIndex: !0,
            zoom: !0
        },
        cssProps: {
            "float": c.cssFloat ? "cssFloat" : "styleFloat"
        },
        style: function(e, t, n, r) {
            if (e && 3 !== e.nodeType && 8 !== e.nodeType && e.style) {
                var i,
                    s,
                    o,
                    u = p.camelCase(t),
                    a = e.style;
                if (t = p.cssProps[u] || (p.cssProps[u] = $t(a, u)), o = p.cssHooks[t] || p.cssHooks[u], void 0 === n)
                    return o && "get" in o && void 0 !== (i = o.get(e, !1, r)) ? i : a[t];
                if (s = typeof n, "string" === s && (i = zt.exec(n)) && (n = (i[1] + 1) * i[2] + parseFloat(p.css(e, t)), s = "number"), null != n && n === n && ("number" !== s || p.cssNumber[u] || (n += "px"), c.clearCloneStyle || "" !== n || 0 !== t.indexOf("background") || (a[t] = "inherit"), !(o && "set" in o && void 0 === (n = o.set(e, n, r)))))
                    try {
                        a[t] = "", a[t] = n
                    } catch (f) {}
            }
        },
        css: function(e, t, n, r) {
            var i,
                s,
                o,
                u = p.camelCase(t);
            return t = p.cssProps[u] || (p.cssProps[u] = $t(e.style, u)), o = p.cssHooks[t] || p.cssHooks[u], o && "get" in o && (s = o.get(e, !0, n)), void 0 === s && (s = Bt(e, t, r)), "normal" === s && t in Xt && (s = Xt[t]), "" === n || n ? (i = parseFloat(s), n === !0 || p.isNumeric(i) ? i || 0 : s) : s
        }
    }), p.each(["height", "width"], function(e, t) {
        p.cssHooks[t] = {
            get: function(e, n, r) {
                return n ? 0 === e.offsetWidth && Rt.test(p.css(e, "display")) ? p.swap(e, Wt, function() {
                    return Gt(e, t, r)
                }) : Gt(e, t, r) : void 0
            },
            set: function(e, n, r) {
                var i = r && Ht(e);
                return Kt(e, n, r ? Qt(e, t, r, c.boxSizing() && "border-box" === p.css(e, "boxSizing", !1, i), i) : 0)
            }
        }
    }), c.opacity || (p.cssHooks.opacity = {
        get: function(e, t) {
            return qt.test((t && e.currentStyle ? e.currentStyle.filter : e.style.filter) || "") ? .01 * parseFloat(RegExp.$1) + "" : t ? "1" : ""
        },
        set: function(e, t) {
            var n = e.style,
                r = e.currentStyle,
                i = p.isNumeric(t) ? "alpha(opacity=" + 100 * t + ")" : "",
                s = r && r.filter || n.filter || "";
            n.zoom = 1, (t >= 1 || "" === t) && "" === p.trim(s.replace(It, "")) && n.removeAttribute && (n.removeAttribute("filter"), "" === t || r && !r.filter) || (n.filter = It.test(s) ? s.replace(It, i) : s + " " + i)
        }
    }), p.cssHooks.marginRight = Ft(c.reliableMarginRight, function(e, t) {
        return t ? p.swap(e, {
            display: "inline-block"
        }, Bt, [e, "marginRight"]) : void 0
    }), p.each({
        margin: "",
        padding: "",
        border: "Width"
    }, function(e, t) {
        p.cssHooks[e + t] = {
            expand: function(n) {
                for (var r = 0, i = {}, s = "string" == typeof n ? n.split(" ") : [n]; 4 > r; r++)
                    i[e + V[r] + t] = s[r] || s[r - 2] || s[0];
                return i
            }
        }, Dt.test(e) || (p.cssHooks[e + t].set = Kt)
    }), p.fn.extend({
        css: function(e, t) {
            return J(this, function(e, t, n) {
                var r,
                    i,
                    s = {},
                    o = 0;
                if (p.isArray(t)) {
                    for (r = Ht(e), i = t.length; i > o; o++)
                        s[t[o]] = p.css(e, t[o], !1, r);
                    return s
                }
                return void 0 !== n ? p.style(e, t, n) : p.css(e, t)
            }, e, t, arguments.length > 1)
        },
        show: function() {
            return Jt(this, !0)
        },
        hide: function() {
            return Jt(this)
        },
        toggle: function(e) {
            return "boolean" == typeof e ? e ? this.show() : this.hide() : this.each(function() {
                $(this) ? p(this).show() : p(this).hide()
            })
        }
    }), p.Tween = Yt, Yt.prototype = {
        constructor: Yt,
        init: function(e, t, n, r, i, s) {
            this.elem = e, this.prop = n, this.easing = i || "swing", this.options = t, this.start = this.now = this.cur(), this.end = r, this.unit = s || (p.cssNumber[n] ? "" : "px")
        },
        cur: function() {
            var e = Yt.propHooks[this.prop];
            return e && e.get ? e.get(this) : Yt.propHooks._default.get(this)
        },
        run: function(e) {
            var t,
                n = Yt.propHooks[this.prop];
            return this.pos = t = this.options.duration ? p.easing[this.easing](e, this.options.duration * e, 0, 1, this.options.duration) : e, this.now = (this.end - this.start) * t + this.start, this.options.step && this.options.step.call(this.elem, this.now, this), n && n.set ? n.set(this) : Yt.propHooks._default.set(this), this
        }
    }, Yt.prototype.init.prototype = Yt.prototype, Yt.propHooks = {
        _default: {
            get: function(e) {
                var t;
                return null == e.elem[e.prop] || e.elem.style && null != e.elem.style[e.prop] ? (t = p.css(e.elem, e.prop, ""), t && "auto" !== t ? t : 0) : e.elem[e.prop]
            },
            set: function(e) {
                p.fx.step[e.prop] ? p.fx.step[e.prop](e) : e.elem.style && (null != e.elem.style[p.cssProps[e.prop]] || p.cssHooks[e.prop]) ? p.style(e.elem, e.prop, e.now + e.unit) : e.elem[e.prop] = e.now
            }
        }
    }, Yt.propHooks.scrollTop = Yt.propHooks.scrollLeft = {
        set: function(e) {
            e.elem.nodeType && e.elem.parentNode && (e.elem[e.prop] = e.now)
        }
    }, p.easing = {
        linear: function(e) {
            return e
        },
        swing: function(e) {
            return .5 - Math.cos(e * Math.PI) / 2
        }
    }, p.fx = Yt.prototype.init, p.fx.step = {};
    var Zt,
        en,
        tn = /^(?:toggle|show|hide)$/,
        nn = new RegExp("^(?:([+-])=|)(" + X + ")([a-z%]*)$", "i"),
        rn = /queueHooks$/,
        sn = [ln],
        on = {
            "*": [function(e, t) {
                var n = this.createTween(e, t),
                    r = n.cur(),
                    i = nn.exec(t),
                    s = i && i[3] || (p.cssNumber[e] ? "" : "px"),
                    o = (p.cssNumber[e] || "px" !== s && +r) && nn.exec(p.css(n.elem, e)),
                    u = 1,
                    a = 20;
                if (o && o[3] !== s) {
                    s = s || o[3], i = i || [], o = +r || 1;
                    do u = u || ".5", o /= u, p.style(n.elem, e, o + s);
                    while (u !== (u = n.cur() / r) && 1 !== u && --a)
                }
                return i && (o = n.start = +o || +r || 0, n.unit = s, n.end = i[1] ? o + (i[1] + 1) * i[2] : +i[2]), n
            }]
        };
    p.Animation = p.extend(hn, {
        tweener: function(e, t) {
            p.isFunction(e) ? (t = e, e = ["*"]) : e = e.split(" ");
            for (var n, r = 0, i = e.length; i > r; r++)
                n = e[r], on[n] = on[n] || [], on[n].unshift(t)
        },
        prefilter: function(e, t) {
            t ? sn.unshift(e) : sn.push(e)
        }
    }), p.speed = function(e, t, n) {
        var r = e && "object" == typeof e ? p.extend({}, e) : {
            complete: n || !n && t || p.isFunction(e) && e,
            duration: e,
            easing: n && t || t && !p.isFunction(t) && t
        };
        return r.duration = p.fx.off ? 0 : "number" == typeof r.duration ? r.duration : r.duration in p.fx.speeds ? p.fx.speeds[r.duration] : p.fx.speeds._default, (null == r.queue || r.queue === !0) && (r.queue = "fx"), r.old = r.complete, r.complete = function() {
            p.isFunction(r.old) && r.old.call(this), r.queue && p.dequeue(this, r.queue)
        }, r
    }, p.fn.extend({
        fadeTo: function(e, t, n, r) {
            return this.filter($).css("opacity", 0).show().end().animate({
                opacity: t
            }, e, n, r)
        },
        animate: function(e, t, n, r) {
            var i = p.isEmptyObject(e),
                s = p.speed(t, n, r),
                o = function() {
                    var t = hn(this, p.extend({}, e), s);
                    (i || p._data(this, "finish")) && t.stop(!0)
                };
            return o.finish = o, i || s.queue === !1 ? this.each(o) : this.queue(s.queue, o)
        },
        stop: function(e, t, n) {
            var r = function(e) {
                var t = e.stop;
                delete e.stop, t(n)
            };
            return "string" != typeof e && (n = t, t = e, e = void 0), t && e !== !1 && this.queue(e || "fx", []), this.each(function() {
                var t = !0,
                    i = null != e && e + "queueHooks",
                    s = p.timers,
                    o = p._data(this);
                if (i)
                    o[i] && o[i].stop && r(o[i]);
                else
                    for (i in o)
                        o[i] && o[i].stop && rn.test(i) && r(o[i]);
                for (i = s.length; i--;)
                    s[i].elem !== this || null != e && s[i].queue !== e || (s[i].anim.stop(n), t = !1, s.splice(i, 1));
                (t || !n) && p.dequeue(this, e)
            })
        },
        finish: function(e) {
            return e !== !1 && (e = e || "fx"), this.each(function() {
                var t,
                    n = p._data(this),
                    r = n[e + "queue"],
                    i = n[e + "queueHooks"],
                    s = p.timers,
                    o = r ? r.length : 0;
                for (n.finish = !0, p.queue(this, e, []), i && i.stop && i.stop.call(this, !0), t = s.length; t--;)
                    s[t].elem === this && s[t].queue === e && (s[t].anim.stop(!0), s.splice(t, 1));
                for (t = 0; o > t; t++)
                    r[t] && r[t].finish && r[t].finish.call(this);
                delete n.finish
            })
        }
    }), p.each(["toggle", "show", "hide"], function(e, t) {
        var n = p.fn[t];
        p.fn[t] = function(e, r, i) {
            return null == e || "boolean" == typeof e ? n.apply(this, arguments) : this.animate(an(t, !0), e, r, i)
        }
    }), p.each({
        slideDown: an("show"),
        slideUp: an("hide"),
        slideToggle: an("toggle"),
        fadeIn: {
            opacity: "show"
        },
        fadeOut: {
            opacity: "hide"
        },
        fadeToggle: {
            opacity: "toggle"
        }
    }, function(e, t) {
        p.fn[e] = function(e, n, r) {
            return this.animate(t, e, n, r)
        }
    }), p.timers = [], p.fx.tick = function() {
        var e,
            t = p.timers,
            n = 0;
        for (Zt = p.now(); n < t.length; n++)
            e = t[n], e() || t[n] !== e || t.splice(n--, 1);
        t.length || p.fx.stop(), Zt = void 0
    }, p.fx.timer = function(e) {
        p.timers.push(e), e() ? p.fx.start() : p.timers.pop()
    }, p.fx.interval = 13, p.fx.start = function() {
        en || (en = setInterval(p.fx.tick, p.fx.interval))
    }, p.fx.stop = function() {
        clearInterval(en), en = null
    }, p.fx.speeds = {
        slow: 600,
        fast: 200,
        _default: 400
    }, p.fn.delay = function(e, t) {
        return e = p.fx ? p.fx.speeds[e] || e : e, t = t || "fx", this.queue(t, function(t, n) {
            var r = setTimeout(t, e);
            n.stop = function() {
                clearTimeout(r)
            }
        })
    }, function() {
        var e,
            t,
            n,
            r,
            i = N.createElement("div");
        i.setAttribute("className", "t"), i.innerHTML = "  <link/><table></table><a href='/a'>a</a><input type='checkbox'/>", e = i.getElementsByTagName("a")[0], n = N.createElement("select"), r = n.appendChild(N.createElement("option")), t = i.getElementsByTagName("input")[0], e.style.cssText = "top:1px", c.getSetAttribute = "t" !== i.className, c.style = /top/.test(e.getAttribute("style")), c.hrefNormalized = "/a" === e.getAttribute("href"), c.checkOn = !!t.value, c.optSelected = r.selected, c.enctype = !!N.createElement("form").enctype, n.disabled = !0, c.optDisabled = !r.disabled, t = N.createElement("input"), t.setAttribute("value", ""), c.input = "" === t.getAttribute("value"), t.value = "t", t.setAttribute("type", "radio"), c.radioValue = "t" === t.value, e = t = n = r = i = null
    }();
    var pn = /\r/g;
    p.fn.extend({
        val: function(e) {
            var t,
                n,
                r,
                i = this[0];
            if (arguments.length)
                return r = p.isFunction(e), this.each(function(n) {
                    var i;
                    1 === this.nodeType && (i = r ? e.call(this, n, p(this).val()) : e, null == i ? i = "" : "number" == typeof i ? i += "" : p.isArray(i) && (i = p.map(i, function(e) {
                        return null == e ? "" : e + ""
                    })), t = p.valHooks[this.type] || p.valHooks[this.nodeName.toLowerCase()], t && "set" in t && void 0 !== t.set(this, i, "value") || (this.value = i))
                });
            if (i)
                return t = p.valHooks[i.type] || p.valHooks[i.nodeName.toLowerCase()], t && "get" in t && void 0 !== (n = t.get(i, "value")) ? n : (n = i.value, "string" == typeof n ? n.replace(pn, "") : null == n ? "" : n)
        }
    }), p.extend({
        valHooks: {
            option: {
                get: function(e) {
                    var t = p.find.attr(e, "value");
                    return null != t ? t : p.text(e)
                }
            },
            select: {
                get: function(e) {
                    for (var t, n, r = e.options, i = e.selectedIndex, s = "select-one" === e.type || 0 > i, o = s ? null : [], u = s ? i + 1 : r.length, a = 0 > i ? u : s ? i : 0; u > a; a++)
                        if (n = r[a], !(!n.selected && a !== i || (c.optDisabled ? n.disabled : null !== n.getAttribute("disabled")) || n.parentNode.disabled && p.nodeName(n.parentNode, "optgroup"))) {
                            if (t = p(n).val(), s)
                                return t;
                            o.push(t)
                        }
                    return o
                },
                set: function(e, t) {
                    var n,
                        r,
                        i = e.options,
                        s = p.makeArray(t),
                        o = i.length;
                    while (o--)
                        if (r = i[o], p.inArray(p.valHooks.option.get(r), s) >= 0)
                            try {
                                r.selected = n = !0
                            } catch (u) {
                                r.scrollHeight
                            }
                        else
                            r.selected = !1;
                    return n || (e.selectedIndex = -1), i
                }
            }
        }
    }), p.each(["radio", "checkbox"], function() {
        p.valHooks[this] = {
            set: function(e, t) {
                return p.isArray(t) ? e.checked = p.inArray(p(e).val(), t) >= 0 : void 0
            }
        }, c.checkOn || (p.valHooks[this].get = function(e) {
            return null === e.getAttribute("value") ? "on" : e.value
        })
    });
    var dn,
        vn,
        mn = p.expr.attrHandle,
        gn = /^(?:checked|selected)$/i,
        yn = c.getSetAttribute,
        bn = c.input;
    p.fn.extend({
        attr: function(e, t) {
            return J(this, p.attr, e, t, arguments.length > 1)
        },
        removeAttr: function(e) {
            return this.each(function() {
                p.removeAttr(this, e)
            })
        }
    }), p.extend({
        attr: function(e, t, n) {
            var r,
                i,
                s = e.nodeType;
            if (e && 3 !== s && 8 !== s && 2 !== s)
                return typeof e.getAttribute === j ? p.prop(e, t, n) : (1 === s && p.isXMLDoc(e) || (t = t.toLowerCase(), r = p.attrHooks[t] || (p.expr.match.bool.test(t) ? vn : dn)), void 0 === n ? r && "get" in r && null !== (i = r.get(e, t)) ? i : (i = p.find.attr(e, t), null == i ? void 0 : i) : null !== n ? r && "set" in r && void 0 !== (i = r.set(e, n, t)) ? i : (e.setAttribute(t, n + ""), n) : void p.removeAttr(e, t))
        },
        removeAttr: function(e, t) {
            var n,
                r,
                i = 0,
                s = t && t.match(M);
            if (s && 1 === e.nodeType)
                while (n = s[i++])
                    r = p.propFix[n] || n, p.expr.match.bool.test(n) ? bn && yn || !gn.test(n) ? e[r] = !1 : e[p.camelCase("default-" + n)] = e[r] = !1 : p.attr(e, n, ""), e.removeAttribute(yn ? n : r)
        },
        attrHooks: {
            type: {
                set: function(e, t) {
                    if (!c.radioValue && "radio" === t && p.nodeName(e, "input")) {
                        var n = e.value;
                        return e.setAttribute("type", t), n && (e.value = n), t
                    }
                }
            }
        }
    }), vn = {
        set: function(e, t, n) {
            return t === !1 ? p.removeAttr(e, n) : bn && yn || !gn.test(n) ? e.setAttribute(!yn && p.propFix[n] || n, n) : e[p.camelCase("default-" + n)] = e[n] = !0, n
        }
    }, p.each(p.expr.match.bool.source.match(/\w+/g), function(e, t) {
        var n = mn[t] || p.find.attr;
        mn[t] = bn && yn || !gn.test(t) ? function(e, t, r) {
            var i,
                s;
            return r || (s = mn[t], mn[t] = i, i = null != n(e, t, r) ? t.toLowerCase() : null, mn[t] = s), i
        } : function(e, t, n) {
            return n ? void 0 : e[p.camelCase("default-" + t)] ? t.toLowerCase() : null
        }
    }), bn && yn || (p.attrHooks.value = {
        set: function(e, t, n) {
            return p.nodeName(e, "input") ? void (e.defaultValue = t) : dn && dn.set(e, t, n)
        }
    }), yn || (dn = {
        set: function(e, t, n) {
            var r = e.getAttributeNode(n);
            return r || e.setAttributeNode(r = e.ownerDocument.createAttribute(n)), r.value = t += "", "value" === n || t === e.getAttribute(n) ? t : void 0
        }
    }, mn.id = mn.name = mn.coords = function(e, t, n) {
        var r;
        return n ? void 0 : (r = e.getAttributeNode(t)) && "" !== r.value ? r.value : null
    }, p.valHooks.button = {
        get: function(e, t) {
            var n = e.getAttributeNode(t);
            return n && n.specified ? n.value : void 0
        },
        set: dn.set
    }, p.attrHooks.contenteditable = {
        set: function(e, t, n) {
            dn.set(e, "" === t ? !1 : t, n)
        }
    }, p.each(["width", "height"], function(e, t) {
        p.attrHooks[t] = {
            set: function(e, n) {
                return "" === n ? (e.setAttribute(t, "auto"), n) : void 0
            }
        }
    })), c.style || (p.attrHooks.style = {
        get: function(e) {
            return e.style.cssText || void 0
        },
        set: function(e, t) {
            return e.style.cssText = t + ""
        }
    });
    var wn = /^(?:input|select|textarea|button|object)$/i,
        En = /^(?:a|area)$/i;
    p.fn.extend({
        prop: function(e, t) {
            return J(this, p.prop, e, t, arguments.length > 1)
        },
        removeProp: function(e) {
            return e = p.propFix[e] || e, this.each(function() {
                try {
                    this[e] = void 0, delete this[e]
                } catch (t) {}
            })
        }
    }), p.extend({
        propFix: {
            "for": "htmlFor",
            "class": "className"
        },
        prop: function(e, t, n) {
            var r,
                i,
                s,
                o = e.nodeType;
            if (e && 3 !== o && 8 !== o && 2 !== o)
                return s = 1 !== o || !p.isXMLDoc(e), s && (t = p.propFix[t] || t, i = p.propHooks[t]), void 0 !== n ? i && "set" in i && void 0 !== (r = i.set(e, n, t)) ? r : e[t] = n : i && "get" in i && null !== (r = i.get(e, t)) ? r : e[t]
        },
        propHooks: {
            tabIndex: {
                get: function(e) {
                    var t = p.find.attr(e, "tabindex");
                    return t ? parseInt(t, 10) : wn.test(e.nodeName) || En.test(e.nodeName) && e.href ? 0 : -1
                }
            }
        }
    }), c.hrefNormalized || p.each(["href", "src"], function(e, t) {
        p.propHooks[t] = {
            get: function(e) {
                return e.getAttribute(t, 4)
            }
        }
    }), c.optSelected || (p.propHooks.selected = {
        get: function(e) {
            var t = e.parentNode;
            return t && (t.selectedIndex, t.parentNode && t.parentNode.selectedIndex), null
        }
    }), p.each(["tabIndex", "readOnly", "maxLength", "cellSpacing", "cellPadding", "rowSpan", "colSpan", "useMap", "frameBorder", "contentEditable"], function() {
        p.propFix[this.toLowerCase()] = this
    }), c.enctype || (p.propFix.enctype = "encoding");
    var Sn = /[\t\r\n\f]/g;
    p.fn.extend({
        addClass: function(e) {
            var t,
                n,
                r,
                i,
                s,
                o,
                u = 0,
                a = this.length,
                f = "string" == typeof e && e;
            if (p.isFunction(e))
                return this.each(function(t) {
                    p(this).addClass(e.call(this, t, this.className))
                });
            if (f)
                for (t = (e || "").match(M) || []; a > u; u++)
                    if (n = this[u], r = 1 === n.nodeType && (n.className ? (" " + n.className + " ").replace(Sn, " ") : " ")) {
                        s = 0;
                        while (i = t[s++])
                            r.indexOf(" " + i + " ") < 0 && (r += i + " ");
                        o = p.trim(r), n.className !== o && (n.className = o)
                    }
            return this
        },
        removeClass: function(e) {
            var t,
                n,
                r,
                i,
                s,
                o,
                u = 0,
                a = this.length,
                f = 0 === arguments.length || "string" == typeof e && e;
            if (p.isFunction(e))
                return this.each(function(t) {
                    p(this).removeClass(e.call(this, t, this.className))
                });
            if (f)
                for (t = (e || "").match(M) || []; a > u; u++)
                    if (n = this[u], r = 1 === n.nodeType && (n.className ? (" " + n.className + " ").replace(Sn, " ") : "")) {
                        s = 0;
                        while (i = t[s++])
                            while (r.indexOf(" " + i + " ") >= 0)
                                r = r.replace(" " + i + " ", " ");
                        o = e ? p.trim(r) : "", n.className !== o && (n.className = o)
                    }
            return this
        },
        toggleClass: function(e, t) {
            var n = typeof e;
            return "boolean" == typeof t && "string" === n ? t ? this.addClass(e) : this.removeClass(e) : this.each(p.isFunction(e) ? function(n) {
                p(this).toggleClass(e.call(this, n, this.className, t), t)
            } : function() {
                if ("string" === n) {
                    var t,
                        r = 0,
                        i = p(this),
                        s = e.match(M) || [];
                    while (t = s[r++])
                        i.hasClass(t) ? i.removeClass(t) : i.addClass(t)
                } else
                    (n === j || "boolean" === n) && (this.className && p._data(this, "__className__", this.className), this.className = this.className || e === !1 ? "" : p._data(this, "__className__") || "")
            })
        },
        hasClass: function(e) {
            for (var t = " " + e + " ", n = 0, r = this.length; r > n; n++)
                if (1 === this[n].nodeType && (" " + this[n].className + " ").replace(Sn, " ").indexOf(t) >= 0)
                    return !0;
            return !1
        }
    }), p.each("blur focus focusin focusout load resize scroll unload click dblclick mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave change select submit keydown keypress keyup error contextmenu".split(" "), function(e, t) {
        p.fn[t] = function(e, n) {
            return arguments.length > 0 ? this.on(t, null, e, n) : this.trigger(t)
        }
    }), p.fn.extend({
        hover: function(e, t) {
            return this.mouseenter(e).mouseleave(t || e)
        },
        bind: function(e, t, n) {
            return this.on(e, null, t, n)
        },
        unbind: function(e, t) {
            return this.off(e, null, t)
        },
        delegate: function(e, t, n, r) {
            return this.on(t, e, n, r)
        },
        undelegate: function(e, t, n) {
            return 1 === arguments.length ? this.off(e, "**") : this.off(t, e || "**", n)
        }
    });
    var xn = p.now(),
        Tn = /\?/,
        Nn = /(,)|(\[|{)|(}|])|"(?:[^"\\\r\n]|\\["\\\/bfnrt]|\\u[\da-fA-F]{4})*"\s*:?|true|false|null|-?(?!0\d)\d+(?:\.\d+|)(?:[eE][+-]?\d+|)/g;
    p.parseJSON = function(t) {
        if (e.JSON && e.JSON.parse)
            return e.JSON.parse(t + "");
        var n,
            r = null,
            i = p.trim(t + "");
        return i && !p.trim(i.replace(Nn, function(e, t, i, s) {
            return n && t && (r = 0), 0 === r ? e : (n = i || t, r += !s - !i, "")
        })) ? Function("return " + i)() : p.error("Invalid JSON: " + t)
    }, p.parseXML = function(t) {
        var n,
            r;
        if (!t || "string" != typeof t)
            return null;
        try {
            e.DOMParser ? (r = new DOMParser, n = r.parseFromString(t, "text/xml")) : (n = new ActiveXObject("Microsoft.XMLDOM"), n.async = "false", n.loadXML(t))
        } catch (i) {
            n = void 0
        }
        return n && n.documentElement && !n.getElementsByTagName("parsererror").length || p.error("Invalid XML: " + t), n
    };
    var Cn,
        kn,
        Ln = /#.*$/,
        An = /([?&])_=[^&]*/,
        On = /^(.*?):[ \t]*([^\r\n]*)\r?$/gm,
        Mn = /^(?:about|app|app-storage|.+-extension|file|res|widget):$/,
        _n = /^(?:GET|HEAD)$/,
        Dn = /^\/\//,
        Pn = /^([\w.+-]+:)(?:\/\/(?:[^\/?#]*@|)([^\/?#:]*)(?::(\d+)|)|)/,
        Hn = {},
        Bn = {},
        jn = "*/".concat("*");
    try {
        kn = location.href
    } catch (Fn) {
        kn = N.createElement("a"), kn.href = "", kn = kn.href
    }
    Cn = Pn.exec(kn.toLowerCase()) || [], p.extend({
        active: 0,
        lastModified: {},
        etag: {},
        ajaxSettings: {
            url: kn,
            type: "GET",
            isLocal: Mn.test(Cn[1]),
            global: !0,
            processData: !0,
            async: !0,
            contentType: "application/x-www-form-urlencoded; charset=UTF-8",
            accepts: {
                "*": jn,
                text: "text/plain",
                html: "text/html",
                xml: "application/xml, text/xml",
                json: "application/json, text/javascript"
            },
            contents: {
                xml: /xml/,
                html: /html/,
                json: /json/
            },
            responseFields: {
                xml: "responseXML",
                text: "responseText",
                json: "responseJSON"
            },
            converters: {
                "* text": String,
                "text html": !0,
                "text json": p.parseJSON,
                "text xml": p.parseXML
            },
            flatOptions: {
                url: !0,
                context: !0
            }
        },
        ajaxSetup: function(e, t) {
            return t ? Rn(Rn(e, p.ajaxSettings), t) : Rn(p.ajaxSettings, e)
        },
        ajaxPrefilter: In(Hn),
        ajaxTransport: In(Bn),
        ajax: function(e, t) {
            function x(e, t, n, r) {
                var f,
                    g,
                    y,
                    w,
                    S,
                    x = t;
                2 !== b && (b = 2, o && clearTimeout(o), a = void 0, s = r || "", E.readyState = e > 0 ? 4 : 0, f = e >= 200 && 300 > e || 304 === e, n && (w = Un(l, E, n)), w = zn(l, w, E, f), f ? (l.ifModified && (S = E.getResponseHeader("Last-Modified"), S && (p.lastModified[i] = S), S = E.getResponseHeader("etag"), S && (p.etag[i] = S)), 204 === e || "HEAD" === l.type ? x = "nocontent" : 304 === e ? x = "notmodified" : (x = w.state, g = w.data, y = w.error, f = !y)) : (y = x, (e || !x) && (x = "error", 0 > e && (e = 0))), E.status = e, E.statusText = (t || x) + "", f ? d.resolveWith(c, [g, x, E]) : d.rejectWith(c, [E, x, y]), E.statusCode(m), m = void 0, u && h.trigger(f ? "ajaxSuccess" : "ajaxError", [E, l, f ? g : y]), v.fireWith(c, [E, x]), u && (h.trigger("ajaxComplete", [E, l]), --p.active || p.event.trigger("ajaxStop")))
            }
            "object" == typeof e && (t = e, e = void 0), t = t || {};
            var n,
                r,
                i,
                s,
                o,
                u,
                a,
                f,
                l = p.ajaxSetup({}, t),
                c = l.context || l,
                h = l.context && (c.nodeType || c.jquery) ? p(c) : p.event,
                d = p.Deferred(),
                v = p.Callbacks("once memory"),
                m = l.statusCode || {},
                g = {},
                y = {},
                b = 0,
                w = "canceled",
                E = {
                    readyState: 0,
                    getResponseHeader: function(e) {
                        var t;
                        if (2 === b) {
                            if (!f) {
                                f = {};
                                while (t = On.exec(s))
                                    f[t[1].toLowerCase()] = t[2]
                            }
                            t = f[e.toLowerCase()]
                        }
                        return null == t ? null : t
                    },
                    getAllResponseHeaders: function() {
                        return 2 === b ? s : null
                    },
                    setRequestHeader: function(e, t) {
                        var n = e.toLowerCase();
                        return b || (e = y[n] = y[n] || e, g[e] = t), this
                    },
                    overrideMimeType: function(e) {
                        return b || (l.mimeType = e), this
                    },
                    statusCode: function(e) {
                        var t;
                        if (e)
                            if (2 > b)
                                for (t in e)
                                    m[t] = [m[t], e[t]];
                            else
                                E.always(e[E.status]);
                        return this
                    },
                    abort: function(e) {
                        var t = e || w;
                        return a && a.abort(t), x(0, t), this
                    }
                };
            if (d.promise(E).complete = v.add, E.success = E.done, E.error = E.fail, l.url = ((e || l.url || kn) + "").replace(Ln, "").replace(Dn, Cn[1] + "//"), l.type = t.method || t.type || l.method || l.type, l.dataTypes = p.trim(l.dataType || "*").toLowerCase().match(M) || [""], null == l.crossDomain && (n = Pn.exec(l.url.toLowerCase()), l.crossDomain = !(!n || n[1] === Cn[1] && n[2] === Cn[2] && (n[3] || ("http:" === n[1] ? "80" : "443")) === (Cn[3] || ("http:" === Cn[1] ? "80" : "443")))), l.data && l.processData && "string" != typeof l.data && (l.data = p.param(l.data, l.traditional)), qn(Hn, l, t, E), 2 === b)
                return E;
            u = l.global, u && 0 === p.active++ && p.event.trigger("ajaxStart"), l.type = l.type.toUpperCase(), l.hasContent = !_n.test(l.type), i = l.url, l.hasContent || (l.data && (i = l.url += (Tn.test(i) ? "&" : "?") + l.data, delete l.data), l.cache === !1 && (l.url = An.test(i) ? i.replace(An, "$1_=" + xn++) : i + (Tn.test(i) ? "&" : "?") + "_=" + xn++)), l.ifModified && (p.lastModified[i] && E.setRequestHeader("If-Modified-Since", p.lastModified[i]), p.etag[i] && E.setRequestHeader("If-None-Match", p.etag[i])), (l.data && l.hasContent && l.contentType !== !1 || t.contentType) && E.setRequestHeader("Content-Type", l.contentType), E.setRequestHeader("Accept", l.dataTypes[0] && l.accepts[l.dataTypes[0]] ? l.accepts[l.dataTypes[0]] + ("*" !== l.dataTypes[0] ? ", " + jn + "; q=0.01" : "") : l.accepts["*"]);
            for (r in l.headers)
                E.setRequestHeader(r, l.headers[r]);
            if (!l.beforeSend || l.beforeSend.call(c, E, l) !== !1 && 2 !== b) {
                w = "abort";
                for (r in {
                    success: 1,
                    error: 1,
                    complete: 1
                })
                    E[r](l[r]);
                if (a = qn(Bn, l, t, E)) {
                    E.readyState = 1, u && h.trigger("ajaxSend", [E, l]), l.async && l.timeout > 0 && (o = setTimeout(function() {
                        E.abort("timeout")
                    }, l.timeout));
                    try {
                        b = 1, a.send(g, x)
                    } catch (S) {
                        if (!(2 > b))
                            throw S;
                        x(-1, S)
                    }
                } else
                    x(-1, "No Transport");
                return E
            }
            return E.abort()
        },
        getJSON: function(e, t, n) {
            return p.get(e, t, n, "json")
        },
        getScript: function(e, t) {
            return p.get(e, void 0, t, "script")
        }
    }), p.each(["get", "post"], function(e, t) {
        p[t] = function(e, n, r, i) {
            return p.isFunction(n) && (i = i || r, r = n, n = void 0), p.ajax({
                url: e,
                type: t,
                dataType: i,
                data: n,
                success: r
            })
        }
    }), p.each(["ajaxStart", "ajaxStop", "ajaxComplete", "ajaxError", "ajaxSuccess", "ajaxSend"], function(e, t) {
        p.fn[t] = function(e) {
            return this.on(t, e)
        }
    }), p._evalUrl = function(e) {
        return p.ajax({
            url: e,
            type: "GET",
            dataType: "script",
            async: !1,
            global: !1,
            "throws": !0
        })
    }, p.fn.extend({
        wrapAll: function(e) {
            if (p.isFunction(e))
                return this.each(function(t) {
                    p(this).wrapAll(e.call(this, t))
                });
            if (this[0]) {
                var t = p(e, this[0].ownerDocument).eq(0).clone(!0);
                this[0].parentNode && t.insertBefore(this[0]), t.map(function() {
                    var e = this;
                    while (e.firstChild && 1 === e.firstChild.nodeType)
                        e = e.firstChild;
                    return e
                }).append(this)
            }
            return this
        },
        wrapInner: function(e) {
            return this.each(p.isFunction(e) ? function(t) {
                p(this).wrapInner(e.call(this, t))
            } : function() {
                var t = p(this),
                    n = t.contents();
                n.length ? n.wrapAll(e) : t.append(e)
            })
        },
        wrap: function(e) {
            var t = p.isFunction(e);
            return this.each(function(n) {
                p(this).wrapAll(t ? e.call(this, n) : e)
            })
        },
        unwrap: function() {
            return this.parent().each(function() {
                p.nodeName(this, "body") || p(this).replaceWith(this.childNodes)
            }).end()
        }
    }), p.expr.filters.hidden = function(e) {
        return e.offsetWidth <= 0 && e.offsetHeight <= 0 || !c.reliableHiddenOffsets() && "none" === (e.style && e.style.display || p.css(e, "display"))
    }, p.expr.filters.visible = function(e) {
        return !p.expr.filters.hidden(e)
    };
    var Wn = /%20/g,
        Xn = /\[\]$/,
        Vn = /\r?\n/g,
        $n = /^(?:submit|button|image|reset|file)$/i,
        Jn = /^(?:input|select|textarea|keygen)/i;
    p.param = function(e, t) {
        var n,
            r = [],
            i = function(e, t) {
                t = p.isFunction(t) ? t() : null == t ? "" : t, r[r.length] = encodeURIComponent(e) + "=" + encodeURIComponent(t)
            };
        if (void 0 === t && (t = p.ajaxSettings && p.ajaxSettings.traditional), p.isArray(e) || e.jquery && !p.isPlainObject(e))
            p.each(e, function() {
                i(this.name, this.value)
            });
        else
            for (n in e)
                Kn(n, e[n], t, i);
        return r.join("&").replace(Wn, "+")
    }, p.fn.extend({
        serialize: function() {
            return p.param(this.serializeArray())
        },
        serializeArray: function() {
            return this.map(function() {
                var e = p.prop(this, "elements");
                return e ? p.makeArray(e) : this
            }).filter(function() {
                var e = this.type;
                return this.name && !p(this).is(":disabled") && Jn.test(this.nodeName) && !$n.test(e) && (this.checked || !K.test(e))
            }).map(function(e, t) {
                var n = p(this).val();
                return null == n ? null : p.isArray(n) ? p.map(n, function(e) {
                    return {
                        name: t.name,
                        value: e.replace(Vn, "\r\n")
                    }
                }) : {
                    name: t.name,
                    value: n.replace(Vn, "\r\n")
                }
            }).get()
        }
    }), p.ajaxSettings.xhr = void 0 !== e.ActiveXObject ? function() {
        return !this.isLocal && /^(get|post|head|put|delete|options)$/i.test(this.type) && Zn() || er()
    } : Zn;
    var Qn = 0,
        Gn = {},
        Yn = p.ajaxSettings.xhr();
    e.ActiveXObject && p(e).on("unload", function() {
        for (var e in Gn)
            Gn[e](void 0, !0)
    }), c.cors = !!Yn && "withCredentials" in Yn, Yn = c.ajax = !!Yn, Yn && p.ajaxTransport(function(e) {
        if (!e.crossDomain || c.cors) {
            var t;
            return {
                send: function(n, r) {
                    var i,
                        s = e.xhr(),
                        o = ++Qn;
                    if (s.open(e.type, e.url, e.async, e.username, e.password), e.xhrFields)
                        for (i in e.xhrFields)
                            s[i] = e.xhrFields[i];
                    e.mimeType && s.overrideMimeType && s.overrideMimeType(e.mimeType), e.crossDomain || n["X-Requested-With"] || (n["X-Requested-With"] = "XMLHttpRequest");
                    for (i in n)
                        void 0 !== n[i] && s.setRequestHeader(i, n[i] + "");
                    s.send(e.hasContent && e.data || null), t = function(n, i) {
                        var u,
                            a,
                            f;
                        if (t && (i || 4 === s.readyState))
                            if (delete Gn[o], t = void 0, s.onreadystatechange = p.noop, i)
                                4 !== s.readyState && s.abort();
                            else {
                                f = {}, u = s.status, "string" == typeof s.responseText && (f.text = s.responseText);
                                try {
                                    a = s.statusText
                                } catch (l) {
                                    a = ""
                                }
                                u || !e.isLocal || e.crossDomain ? 1223 === u && (u = 204) : u = f.text ? 200 : 404
                            }
                        f && r(u, a, f, s.getAllResponseHeaders())
                    }, e.async ? 4 === s.readyState ? setTimeout(t) : s.onreadystatechange = Gn[o] = t : t()
                },
                abort: function() {
                    t && t(void 0, !0)
                }
            }
        }
    }), p.ajaxSetup({
        accepts: {
            script: "text/javascript, application/javascript, application/ecmascript, application/x-ecmascript"
        },
        contents: {
            script: /(?:java|ecma)script/
        },
        converters: {
            "text script": function(e) {
                return p.globalEval(e), e
            }
        }
    }), p.ajaxPrefilter("script", function(e) {
        void 0 === e.cache && (e.cache = !1), e.crossDomain && (e.type = "GET", e.global = !1)
    }), p.ajaxTransport("script", function(e) {
        if (e.crossDomain) {
            var t,
                n = N.head || p("head")[0] || N.documentElement;
            return {
                send: function(r, i) {
                    t = N.createElement("script"), t.async = !0, e.scriptCharset && (t.charset = e.scriptCharset), t.src = e.url, t.onload = t.onreadystatechange = function(e, n) {
                        (n || !t.readyState || /loaded|complete/.test(t.readyState)) && (t.onload = t.onreadystatechange = null, t.parentNode && t.parentNode.removeChild(t), t = null, n || i(200, "success"))
                    }, n.insertBefore(t, n.firstChild)
                },
                abort: function() {
                    t && t.onload(void 0, !0)
                }
            }
        }
    });
    var tr = [],
        nr = /(=)\?(?=&|$)|\?\?/;
    p.ajaxSetup({
        jsonp: "callback",
        jsonpCallback: function() {
            var e = tr.pop() || p.expando + "_" + xn++;
            return this[e] = !0, e
        }
    }), p.ajaxPrefilter("json jsonp", function(t, n, r) {
        var i,
            s,
            o,
            u = t.jsonp !== !1 && (nr.test(t.url) ? "url" : "string" == typeof t.data && !(t.contentType || "").indexOf("application/x-www-form-urlencoded") && nr.test(t.data) && "data");
        return u || "jsonp" === t.dataTypes[0] ? (i = t.jsonpCallback = p.isFunction(t.jsonpCallback) ? t.jsonpCallback() : t.jsonpCallback, u ? t[u] = t[u].replace(nr, "$1" + i) : t.jsonp !== !1 && (t.url += (Tn.test(t.url) ? "&" : "?") + t.jsonp + "=" + i), t.converters["script json"] = function() {
            return o || p.error(i + " was not called"), o[0]
        }, t.dataTypes[0] = "json", s = e[i], e[i] = function() {
            o = arguments
        }, r.always(function() {
            e[i] = s, t[i] && (t.jsonpCallback = n.jsonpCallback, tr.push(i)), o && p.isFunction(s) && s(o[0]), o = s = void 0
        }), "script") : void 0
    }), p.parseHTML = function(e, t, n) {
        if (!e || "string" != typeof e)
            return null;
        "boolean" == typeof t && (n = t, t = !1), t = t || N;
        var r = E.exec(e),
            i = !n && [];
        return r ? [t.createElement(r[1])] : (r = p.buildFragment([e], t, i), i && i.length && p(i).remove(), p.merge([], r.childNodes))
    };
    var rr = p.fn.load;
    p.fn.load = function(e, t, n) {
        if ("string" != typeof e && rr)
            return rr.apply(this, arguments);
        var r,
            i,
            s,
            o = this,
            u = e.indexOf(" ");
        return u >= 0 && (r = e.slice(u, e.length), e = e.slice(0, u)), p.isFunction(t) ? (n = t, t = void 0) : t && "object" == typeof t && (s = "POST"), o.length > 0 && p.ajax({
            url: e,
            type: s,
            dataType: "html",
            data: t
        }).done(function(e) {
            i = arguments, o.html(r ? p("<div>").append(p.parseHTML(e)).find(r) : e)
        }).complete(n && function(e, t) {
            o.each(n, i || [e.responseText, t, e])
        }), this
    }, p.expr.filters.animated = function(e) {
        return p.grep(p.timers, function(t) {
            return e === t.elem
        }).length
    };
    var ir = e.document.documentElement;
    p.offset = {
        setOffset: function(e, t, n) {
            var r,
                i,
                s,
                o,
                u,
                a,
                f,
                l = p.css(e, "position"),
                c = p(e),
                h = {};
            "static" === l && (e.style.position = "relative"), u = c.offset(), s = p.css(e, "top"), a = p.css(e, "left"), f = ("absolute" === l || "fixed" === l) && p.inArray("auto", [s, a]) > -1, f ? (r = c.position(), o = r.top, i = r.left) : (o = parseFloat(s) || 0, i = parseFloat(a) || 0), p.isFunction(t) && (t = t.call(e, n, u)), null != t.top && (h.top = t.top - u.top + o), null != t.left && (h.left = t.left - u.left + i), "using" in t ? t.using.call(e, h) : c.css(h)
        }
    }, p.fn.extend({
        offset: function(e) {
            if (arguments.length)
                return void 0 === e ? this : this.each(function(t) {
                    p.offset.setOffset(this, e, t)
                });
            var t,
                n,
                r = {
                    top: 0,
                    left: 0
                },
                i = this[0],
                s = i && i.ownerDocument;
            if (s)
                return t = s.documentElement, p.contains(t, i) ? (typeof i.getBoundingClientRect !== j && (r = i.getBoundingClientRect()), n = sr(s), {
                    top: r.top + (n.pageYOffset || t.scrollTop) - (t.clientTop || 0),
                    left: r.left + (n.pageXOffset || t.scrollLeft) - (t.clientLeft || 0)
                }) : r
        },
        position: function() {
            if (this[0]) {
                var e,
                    t,
                    n = {
                        top: 0,
                        left: 0
                    },
                    r = this[0];
                return "fixed" === p.css(r, "position") ? t = r.getBoundingClientRect() : (e = this.offsetParent(), t = this.offset(), p.nodeName(e[0], "html") || (n = e.offset()), n.top += p.css(e[0], "borderTopWidth", !0), n.left += p.css(e[0], "borderLeftWidth", !0)), {
                    top: t.top - n.top - p.css(r, "marginTop", !0),
                    left: t.left - n.left - p.css(r, "marginLeft", !0)
                }
            }
        },
        offsetParent: function() {
            return this.map(function() {
                var e = this.offsetParent || ir;
                while (e && !p.nodeName(e, "html") && "static" === p.css(e, "position"))
                    e = e.offsetParent;
                return e || ir
            })
        }
    }), p.each({
        scrollLeft: "pageXOffset",
        scrollTop: "pageYOffset"
    }, function(e, t) {
        var n = /Y/.test(t);
        p.fn[e] = function(r) {
            return J(this, function(e, r, i) {
                var s = sr(e);
                return void 0 === i ? s ? t in s ? s[t] : s.document.documentElement[r] : e[r] : void (s ? s.scrollTo(n ? p(s).scrollLeft() : i, n ? i : p(s).scrollTop()) : e[r] = i)
            }, e, r, arguments.length, null)
        }
    }), p.each(["top", "left"], function(e, t) {
        p.cssHooks[t] = Ft(c.pixelPosition, function(e, n) {
            return n ? (n = Bt(e, t), Pt.test(n) ? p(e).position()[t] + "px" : n) : void 0
        })
    }), p.each({
        Height: "height",
        Width: "width"
    }, function(e, t) {
        p.each({
            padding: "inner" + e,
            content: t,
            "": "outer" + e
        }, function(n, r) {
            p.fn[r] = function(r, i) {
                var s = arguments.length && (n || "boolean" != typeof r),
                    o = n || (r === !0 || i === !0 ? "margin" : "border");
                return J(this, function(t, n, r) {
                    var i;
                    return p.isWindow(t) ? t.document.documentElement["client" + e] : 9 === t.nodeType ? (i = t.documentElement, Math.max(t.body["scroll" + e], i["scroll" + e], t.body["offset" + e], i["offset" + e], i["client" + e])) : void 0 === r ? p.css(t, n, o) : p.style(t, n, r, o)
                }, t, s ? r : void 0, s, null)
            }
        })
    }), p.fn.size = function() {
        return this.length
    }, p.fn.andSelf = p.fn.addBack, "function" == typeof define && define.amd && define("jquery", [], function() {
        return p
    });
    var or = e.jQuery,
        ur = e.$;
    return p.noConflict = function(t) {
        return e.$ === p && (e.$ = ur), t && e.jQuery === p && (e.jQuery = or), p
    }, typeof t === j && (e.jQuery = e.$ = p), p
}), window.Modernizr = function(e, t, n) {
    function r(e) {
        m.cssText = e
    }
    function i(e, t) {
        return r(w.join(e + ";") + (t || ""))
    }
    function s(e, t) {
        return typeof e === t
    }
    function o(e, t) {
        return !!~("" + e).indexOf(t)
    }
    function u(e, t) {
        for (var r in e) {
            var i = e[r];
            if (!o(i, "-") && m[i] !== n)
                return t == "pfx" ? i : !0
        }
        return !1
    }
    function a(e, t, r) {
        for (var i in e) {
            var o = t[e[i]];
            if (o !== n)
                return r === !1 ? e[i] : s(o, "function") ? o.bind(r || t) : o
        }
        return !1
    }
    function f(e, t, n) {
        var r = e.charAt(0).toUpperCase() + e.slice(1),
            i = (e + " " + S.join(r + " ") + r).split(" ");
        return s(t, "string") || s(t, "undefined") ? u(i, t) : (i = (e + " " + x.join(r + " ") + r).split(" "), a(i, t, n))
    }
    var l = "2.8.2",
        c = {},
        h = !0,
        p = t.documentElement,
        d = "modernizr",
        v = t.createElement(d),
        m = v.style,
        g,
        y = ":)",
        b = {}.toString,
        w = " -webkit- -moz- -o- -ms- ".split(" "),
        E = "Webkit Moz O ms",
        S = E.split(" "),
        x = E.toLowerCase().split(" "),
        T = {},
        N = {},
        C = {},
        k = [],
        L = k.slice,
        A,
        O = function(e, n, r, i) {
            var s,
                o,
                u,
                a,
                f = t.createElement("div"),
                l = t.body,
                c = l || t.createElement("body");
            if (parseInt(r, 10))
                while (r--)
                    u = t.createElement("div"), u.id = i ? i[r] : d + (r + 1), f.appendChild(u);
            return s = ["&#173;", '<style id="s', d, '">', e, "</style>"].join(""), f.id = d, (l ? f : c).innerHTML += s, c.appendChild(f), l || (c.style.background = "", c.style.overflow = "hidden", a = p.style.overflow, p.style.overflow = "hidden", p.appendChild(c)), o = n(f, e), l ? f.parentNode.removeChild(f) : (c.parentNode.removeChild(c), p.style.overflow = a), !!o
        },
        M = {}.hasOwnProperty,
        _;
    !s(M, "undefined") && !s(M.call, "undefined") ? _ = function(e, t) {
        return M.call(e, t)
    } : _ = function(e, t) {
        return t in e && s(e.constructor.prototype[t], "undefined")
    }, Function.prototype.bind || (Function.prototype.bind = function(e) {
        var t = this;
        if (typeof t != "function")
            throw new TypeError;
        var n = L.call(arguments, 1),
            r = function() {
                if (this instanceof r) {
                    var i = function() {};
                    i.prototype = t.prototype;
                    var s = new i,
                        o = t.apply(s, n.concat(L.call(arguments)));
                    return Object(o) === o ? o : s
                }
                return t.apply(e, n.concat(L.call(arguments)))
            };
        return r
    }), T.flexbox = function() {
        return f("flexWrap")
    }, T.flexboxlegacy = function() {
        return f("boxDirection")
    }, T.rgba = function() {
        return r("background-color:rgba(150,255,150,.5)"), o(m.backgroundColor, "rgba")
    }, T.hsla = function() {
        return r("background-color:hsla(120,40%,100%,.5)"), o(m.backgroundColor, "rgba") || o(m.backgroundColor, "hsla")
    }, T.multiplebgs = function() {
        return r("background:url(https://),url(https://),red url(https://)"), /(url\s*\(.*?){3}/.test(m.background)
    }, T.backgroundsize = function() {
        return f("backgroundSize")
    }, T.borderimage = function() {
        return f("borderImage")
    }, T.borderradius = function() {
        return f("borderRadius")
    }, T.boxshadow = function() {
        return f("boxShadow")
    }, T.textshadow = function() {
        return t.createElement("div").style.textShadow === ""
    }, T.opacity = function() {
        return i("opacity:.55"), /^0.55$/.test(m.opacity)
    }, T.cssanimations = function() {
        return f("animationName")
    }, T.csscolumns = function() {
        return f("columnCount")
    }, T.cssgradients = function() {
        var e = "background-image:",
            t = "gradient(linear,left top,right bottom,from(#9f9),to(white));",
            n = "linear-gradient(left top,#9f9, white);";
        return r((e + "-webkit- ".split(" ").join(t + e) + w.join(n + e)).slice(0, -e.length)), o(m.backgroundImage, "gradient")
    }, T.cssreflections = function() {
        return f("boxReflect")
    }, T.csstransforms = function() {
        return !!f("transform")
    }, T.csstransforms3d = function() {
        var e = !!f("perspective");
        return e && "webkitPerspective" in p.style && O("@media (transform-3d),(-webkit-transform-3d){#modernizr{left:9px;position:absolute;height:3px;}}", function(t, n) {
            e = t.offsetLeft === 9 && t.offsetHeight === 3
        }), e
    }, T.csstransitions = function() {
        return f("transition")
    }, T.fontface = function() {
        var e;
        return O('@font-face {font-family:"font";src:url("https://")}', function(n, r) {
            var i = t.getElementById("smodernizr"),
                s = i.sheet || i.styleSheet,
                o = s ? s.cssRules && s.cssRules[0] ? s.cssRules[0].cssText : s.cssText || "" : "";
            e = /src/i.test(o) && o.indexOf(r.split(" ")[0]) === 0
        }), e
    }, T.generatedcontent = function() {
        var e;
        return O(["#", d, "{font:0/0 a}#", d, ':after{content:"', y, '";visibility:hidden;font:3px/1 a}'].join(""), function(t) {
            e = t.offsetHeight >= 3
        }), e
    };
    for (var D in T)
        _(T, D) && (A = D.toLowerCase(), c[A] = T[D](), k.push((c[A] ? "" : "no-") + A));
    return c.addTest = function(e, t) {
        if (typeof e == "object")
            for (var r in e)
                _(e, r) && c.addTest(r, e[r]);
        else {
            e = e.toLowerCase();
            if (c[e] !== n)
                return c;
            t = typeof t == "function" ? t() : t, typeof h != "undefined" && h && (p.className += " " + (t ? "" : "no-") + e), c[e] = t
        }
        return c
    }, r(""), v = g = null, function(e, t) {
        function n(e, t) {
            var n = e.createElement("p"),
                r = e.getElementsByTagName("head")[0] || e.documentElement;
            return n.innerHTML = "x<style>" + t + "</style>", r.insertBefore(n.lastChild, r.firstChild)
        }
        function r() {
            var e = y.elements;
            return typeof e == "string" ? e.split(" ") : e
        }
        function i(e) {
            var t = m[e[d]];
            return t || (t = {}, v++, e[d] = v, m[v] = t), t
        }
        function s(e, n, r) {
            n || (n = t);
            if (g)
                return n.createElement(e);
            r || (r = i(n));
            var s;
            return r.cache[e] ? s = r.cache[e].cloneNode() : h.test(e) ? s = (r.cache[e] = r.createElem(e)).cloneNode() : s = r.createElem(e), s.canHaveChildren && !c.test(e) && !s.tagUrn ? r.frag.appendChild(s) : s
        }
        function o(e, n) {
            e || (e = t);
            if (g)
                return e.createDocumentFragment();
            n = n || i(e);
            var s = n.frag.cloneNode(),
                o = 0,
                u = r(),
                a = u.length;
            for (; o < a; o++)
                s.createElement(u[o]);
            return s
        }
        function u(e, t) {
            t.cache || (t.cache = {}, t.createElem = e.createElement, t.createFrag = e.createDocumentFragment, t.frag = t.createFrag()), e.createElement = function(n) {
                return y.shivMethods ? s(n, e, t) : t.createElem(n)
            }, e.createDocumentFragment = Function("h,f", "return function(){var n=f.cloneNode(),c=n.createElement;h.shivMethods&&(" + r().join().replace(/[\w\-]+/g, function(e) {
                return t.createElem(e), t.frag.createElement(e), 'c("' + e + '")'
            }) + ");return n}")(y, t.frag)
        }
        function a(e) {
            e || (e = t);
            var r = i(e);
            return y.shivCSS && !p && !r.hasCSS && (r.hasCSS = !!n(e, "article,aside,dialog,figcaption,figure,footer,header,hgroup,main,nav,section{display:block}mark{background:#FF0;color:#000}template{display:none}")), g || u(e, r), e
        }
        var f = "3.7.0",
            l = e.html5 || {},
            c = /^<|^(?:button|map|select|textarea|object|iframe|option|optgroup)$/i,
            h = /^(?:a|b|code|div|fieldset|h1|h2|h3|h4|h5|h6|i|label|li|ol|p|q|span|strong|style|table|tbody|td|th|tr|ul)$/i,
            p,
            d = "_html5shiv",
            v = 0,
            m = {},
            g;
        (function() {
            try {
                var e = t.createElement("a");
                e.innerHTML = "<xyz></xyz>", p = "hidden" in e, g = e.childNodes.length == 1 || function() {
                    t.createElement("a");
                    var e = t.createDocumentFragment();
                    return typeof e.cloneNode == "undefined" || typeof e.createDocumentFragment == "undefined" || typeof e.createElement == "undefined"
                }()
            } catch (n) {
                p = !0, g = !0
            }
        })();
        var y = {
            elements: l.elements || "abbr article aside audio bdi canvas data datalist details dialog figcaption figure footer header hgroup main mark meter nav output progress section summary template time video",
            version: f,
            shivCSS: l.shivCSS !== !1,
            supportsUnknownElements: g,
            shivMethods: l.shivMethods !== !1,
            type: "default",
            shivDocument: a,
            createElement: s,
            createDocumentFragment: o
        };
        e.html5 = y, a(t)
    }(this, t), c._version = l, c._prefixes = w, c._domPrefixes = x, c._cssomPrefixes = S, c.testProp = function(e) {
        return u([e])
    }, c.testAllProps = f, c.testStyles = O, p.className = p.className.replace(/(^|\s)no-js(\s|$)/, "$1$2") + (h ? " js " + k.join(" ") : ""), c
}(this, this.document), function(e, t, n) {
    function r(e) {
        return "[object Function]" == d.call(e)
    }
    function i(e) {
        return "string" == typeof e
    }
    function s() {}
    function o(e) {
        return !e || "loaded" == e || "complete" == e || "uninitialized" == e
    }
    function u() {
        var e = v.shift();
        m = 1, e ? e.t ? h(function() {
            ("c" == e.t ? k.injectCss : k.injectJs)(e.s, 0, e.a, e.x, e.e, 1)
        }, 0) : (e(), u()) : m = 0
    }
    function a(e, n, r, i, s, a, f) {
        function l(t) {
            if (!d && o(c.readyState) && (w.r = d = 1, !m && u(), c.onload = c.onreadystatechange = null, t)) {
                "img" != e && h(function() {
                    b.removeChild(c)
                }, 50);
                for (var r in T[n])
                    T[n].hasOwnProperty(r) && T[n][r].onload()
            }
        }
        var f = f || k.errorTimeout,
            c = t.createElement(e),
            d = 0,
            g = 0,
            w = {
                t: r,
                s: n,
                e: s,
                a: a,
                x: f
            };
        1 === T[n] && (g = 1, T[n] = []), "object" == e ? c.data = n : (c.src = n, c.type = e), c.width = c.height = "0", c.onerror = c.onload = c.onreadystatechange = function() {
            l.call(this, g)
        }, v.splice(i, 0, w), "img" != e && (g || 2 === T[n] ? (b.insertBefore(c, y ? null : p), h(l, f)) : T[n].push(c))
    }
    function f(e, t, n, r, s) {
        return m = 0, t = t || "j", i(e) ? a("c" == t ? E : w, e, t, this.i++, n, r, s) : (v.splice(this.i++, 0, e), 1 == v.length && u()), this
    }
    function l() {
        var e = k;
        return e.loader = {
            load: f,
            i: 0
        }, e
    }
    var c = t.documentElement,
        h = e.setTimeout,
        p = t.getElementsByTagName("script")[0],
        d = {}.toString,
        v = [],
        m = 0,
        g = "MozAppearance" in c.style,
        y = g && !!t.createRange().compareNode,
        b = y ? c : p.parentNode,
        c = e.opera && "[object Opera]" == d.call(e.opera),
        c = !!t.attachEvent && !c,
        w = g ? "object" : c ? "script" : "img",
        E = c ? "script" : w,
        S = Array.isArray || function(e) {
            return "[object Array]" == d.call(e)
        },
        x = [],
        T = {},
        N = {
            timeout: function(e, t) {
                return t.length && (e.timeout = t[0]), e
            }
        },
        C,
        k;
    k = function(e) {
        function t(e) {
            var e = e.split("!"),
                t = x.length,
                n = e.pop(),
                r = e.length,
                n = {
                    url: n,
                    origUrl: n,
                    prefixes: e
                },
                i,
                s,
                o;
            for (s = 0; s < r; s++)
                o = e[s].split("="), (i = N[o.shift()]) && (n = i(n, o));
            for (s = 0; s < t; s++)
                n = x[s](n);
            return n
        }
        function o(e, i, s, o, u) {
            var a = t(e),
                f = a.autoCallback;
            a.url.split(".").pop().split("?").shift(), a.bypass || (i && (i = r(i) ? i : i[e] || i[o] || i[e.split("/").pop().split("?")[0]]), a.instead ? a.instead(e, i, s, o, u) : (T[a.url] ? a.noexec = !0 : T[a.url] = 1, s.load(a.url, a.forceCSS || !a.forceJS && "css" == a.url.split(".").pop().split("?").shift() ? "c" : n, a.noexec, a.attrs, a.timeout), (r(i) || r(f)) && s.load(function() {
                l(), i && i(a.origUrl, u, o), f && f(a.origUrl, u, o), T[a.url] = 2
            })))
        }
        function u(e, t) {
            function n(e, n) {
                if (e) {
                    if (i(e))
                        n || (f = function() {
                            var e = [].slice.call(arguments);
                            l.apply(this, e), c()
                        }), o(e, f, t, 0, u);
                    else if (Object(e) === e)
                        for (p in h = function() {
                            var t = 0,
                                n;
                            for (n in e)
                                e.hasOwnProperty(n) && t++;
                            return t
                        }(), e)
                            e.hasOwnProperty(p) && (!n && !--h && (r(f) ? f = function() {
                                var e = [].slice.call(arguments);
                                l.apply(this, e), c()
                            } : f[p] = function(e) {
                                return function() {
                                    var t = [].slice.call(arguments);
                                    e && e.apply(this, t), c()
                                }
                            }(l[p])), o(e[p], f, t, p, u))
                } else
                    !n && c()
            }
            var u = !!e.test,
                a = e.load || e.both,
                f = e.callback || s,
                l = f,
                c = e.complete || s,
                h,
                p;
            n(u ? e.yep : e.nope, !!a), a && n(a)
        }
        var a,
            f,
            c = this.yepnope.loader;
        if (i(e))
            o(e, 0, c, 0);
        else if (S(e))
            for (a = 0; a < e.length; a++)
                f = e[a], i(f) ? o(f, 0, c, 0) : S(f) ? k(f) : Object(f) === f && u(f, c);
        else
            Object(e) === e && u(e, c)
    }, k.addPrefix = function(e, t) {
        N[e] = t
    }, k.addFilter = function(e) {
        x.push(e)
    }, k.errorTimeout = 1e4, null == t.readyState && t.addEventListener && (t.readyState = "loading", t.addEventListener("DOMContentLoaded", C = function() {
        t.removeEventListener("DOMContentLoaded", C, 0), t.readyState = "complete"
    }, 0)), e.yepnope = l(), e.yepnope.executeStack = u, e.yepnope.injectJs = function(e, n, r, i, a, f) {
        var l = t.createElement("script"),
            c,
            d,
            i = i || k.errorTimeout;
        l.src = e;
        for (d in r)
            l.setAttribute(d, r[d]);
        n = f ? u : n || s, l.onreadystatechange = l.onload = function() {
            !c && o(l.readyState) && (c = 1, n(), l.onload = l.onreadystatechange = null)
        }, h(function() {
            c || (c = 1, n(1))
        }, i), a ? l.onload() : p.parentNode.insertBefore(l, p)
    }, e.yepnope.injectCss = function(e, n, r, i, o, a) {
        var i = t.createElement("link"),
            f,
            n = a ? u : n || s;
        i.href = e, i.rel = "stylesheet", i.type = "text/css";
        for (f in r)
            i.setAttribute(f, r[f]);
        o || (p.parentNode.insertBefore(i, p), h(n, 0))
    }
}(this, document), Modernizr.load = function() {
    yepnope.apply(window, [].slice.call(arguments, 0))
}, define("modernizr", function() {}), window.matchMedia || (window.matchMedia = function() {
    var e = window.styleMedia || window.media;
    if (!e) {
        var t = document.createElement("style"),
            n = document.getElementsByTagName("script")[0],
            r = null;
        t.type = "text/css", t.id = "matchmediajs-test", n.parentNode.insertBefore(t, n), r = "getComputedStyle" in window && window.getComputedStyle(t, null) || t.currentStyle, e = {
            matchMedium: function(e) {
                var n = "@media " + e + "{ #matchmediajs-test { width: 1px; } }";
                return t.styleSheet ? t.styleSheet.cssText = n : t.textContent = n, "1px" === r.width
            }
        }
    }
    return function(t) {
        return {
            matches: e.matchMedium(t || "all"),
            media: t || "all"
        }
    }
}()), function(e, t, n) {
    function r(t) {
        "object" == typeof module && "object" == typeof module.exports ? module.exports = t : "function" == typeof define && define.amd && define("picturefill", [], function() {
            return t
        }), "object" == typeof e && (e.picturefill = t)
    }
    function i(e) {
        var t,
            n,
            r,
            i,
            s,
            a = e || {};
        t = a.elements || o.getAllElements();
        for (var f = 0, l = t.length; l > f; f++)
            if (n = t[f], r = n.parentNode, i = void 0, s = void 0, "IMG" === n.nodeName.toUpperCase() && (n[o.ns] || (n[o.ns] = {}), a.reevaluate || !n[o.ns].evaluated)) {
                if (r && "PICTURE" === r.nodeName.toUpperCase()) {
                    if (o.removeVideoShim(r), i = o.getMatch(n, r), i === !1)
                        continue
                } else
                    i = void 0;
                (r && "PICTURE" === r.nodeName.toUpperCase() || !o.sizesSupported && n.srcset && u.test(n.srcset)) && o.dodgeSrcset(n), i ? (s = o.processSourceSet(i), o.applyBestCandidate(s, n)) : (s = o.processSourceSet(n), (void 0 === n.srcset || n[o.ns].srcset) && o.applyBestCandidate(s, n)), n[o.ns].evaluated = !0
            }
    }
    function s() {
        function n() {
            var t;
            e._picturefillWorking || (e._picturefillWorking = !0, e.clearTimeout(t), t = e.setTimeout(function() {
                i({
                    reevaluate: !0
                }), e._picturefillWorking = !1
            }, 60))
        }
        o.initTypeDetects(), i();
        var r = setInterval(function() {
            return i(), /^loaded|^i|^c/.test(t.readyState) ? void clearInterval(r) : void 0
        }, 250);
        e.addEventListener ? e.addEventListener("resize", n, !1) : e.attachEvent && e.attachEvent("onresize", n)
    }
    if (e.HTMLPictureElement)
        return void r(function() {});
    t.createElement("picture");
    var o = e.picturefill || {},
        u = /\s+\+?\d+(e\d+)?w/;
    o.ns = "picturefill", function() {
        o.srcsetSupported = "srcset" in n, o.sizesSupported = "sizes" in n
    }(), o.trim = function(e) {
        return e.trim ? e.trim() : e.replace(/^\s+|\s+$/g, "")
    }, o.makeUrl = function() {
        var e = t.createElement("a");
        return function(t) {
            return e.href = t, e.href
        }
    }(), o.restrictsMixedContent = function() {
        return "https:" === e.location.protocol
    }, o.matchesMedia = function(t) {
        return e.matchMedia && e.matchMedia(t).matches
    }, o.getDpr = function() {
        return e.devicePixelRatio || 1
    }, o.getWidthFromLength = function(e) {
        var n;
        if (!e || e.indexOf("%") > -1 != 0 || !(parseFloat(e) > 0 || e.indexOf("calc(") > -1))
            return !1;
        e = e.replace("vw", "%"), o.lengthEl || (o.lengthEl = t.createElement("div"), o.lengthEl.style.cssText = "border:0;display:block;font-size:1em;left:0;margin:0;padding:0;position:absolute;visibility:hidden", o.lengthEl.className = "helper-from-picturefill-js"), o.lengthEl.style.width = "0px";
        try {
            o.lengthEl.style.width = e
        } catch (r) {}
        return t.body.appendChild(o.lengthEl), n = o.lengthEl.offsetWidth, 0 >= n && (n = !1), t.body.removeChild(o.lengthEl), n
    }, o.detectTypeSupport = function(t, n) {
        var r = new e.Image;
        return r.onerror = function() {
            o.types[t] = !1, i()
        }, r.onload = function() {
            o.types[t] = 1 === r.width, i()
        }, r.src = n, "pending"
    }, o.types = o.types || {}, o.initTypeDetects = function() {
        o.types["image/jpeg"] = !0, o.types["image/gif"] = !0, o.types["image/png"] = !0, o.types["image/svg+xml"] = t.implementation.hasFeature("http://www.w3.org/TR/SVG11/feature#Image", "1.1"), o.types["image/webp"] = o.detectTypeSupport("image/webp", "data:image/webp;base64,UklGRh4AAABXRUJQVlA4TBEAAAAvAAAAAAfQ//73v/+BiOh/AAA=")
    }, o.verifyTypeSupport = function(e) {
        var t = e.getAttribute("type");
        if (null === t || "" === t)
            return !0;
        var n = o.types[t];
        return "string" == typeof n && "pending" !== n ? (o.types[t] = o.detectTypeSupport(t, n), "pending") : "function" == typeof n ? (n(), "pending") : n
    }, o.parseSize = function(e) {
        var t = /(\([^)]+\))?\s*(.+)/g.exec(e);
        return {
            media: t && t[1],
            length: t && t[2]
        }
    }, o.findWidthFromSourceSize = function(n) {
        for (var r, i = o.trim(n).split(/\s*,\s*/), s = 0, u = i.length; u > s; s++) {
            var f = i[s],
                l = o.parseSize(f),
                c = l.length,
                h = l.media;
            if (c && (!h || o.matchesMedia(h)) && (r = o.getWidthFromLength(c)))
                break
        }
        return r || Math.max(e.innerWidth || 0, t.documentElement.clientWidth)
    }, o.parseSrcset = function(e) {
        for (var t = []; "" !== e;) {
            e = e.replace(/^\s+/g, "");
            var n,
                r = e.search(/\s/g),
                i = null;
            if (-1 !== r) {
                n = e.slice(0, r);
                var s = n.slice(-1);
                if (("," === s || "" === n) && (n = n.replace(/,+$/, ""), i = ""), e = e.slice(r + 1), null === i) {
                    var o = e.indexOf(",");
                    -1 !== o ? (i = e.slice(0, o), e = e.slice(o + 1)) : (i = e, e = "")
                }
            } else
                n = e, e = "";
            (n || i) && t.push({
                url: n,
                descriptor: i
            })
        }
        return t
    }, o.parseDescriptor = function(e, t) {
        var n,
            r = t || "100vw",
            i = e && e.replace(/(^\s+|\s+$)/g, ""),
            s = o.findWidthFromSourceSize(r);
        if (i)
            for (var u = i.split(" "), a = u.length - 1; a >= 0; a--) {
                var f = u[a],
                    l = f && f.slice(f.length - 1);
                if ("h" !== l && "w" !== l || o.sizesSupported) {
                    if ("x" === l) {
                        var c = f && parseFloat(f, 10);
                        n = c && !isNaN(c) ? c : 1
                    }
                } else
                    n = parseFloat(parseInt(f, 10) / s)
            }
        return n || 1
    }, o.getCandidatesFromSourceSet = function(e, t) {
        for (var n = o.parseSrcset(e), r = [], i = 0, s = n.length; s > i; i++) {
            var u = n[i];
            r.push({
                url: u.url,
                resolution: o.parseDescriptor(u.descriptor, t)
            })
        }
        return r
    }, o.dodgeSrcset = function(e) {
        e.srcset && (e[o.ns].srcset = e.srcset, e.srcset = "", e.setAttribute("data-pfsrcset", e[o.ns].srcset))
    }, o.processSourceSet = function(e) {
        var t = e.getAttribute("srcset"),
            n = e.getAttribute("sizes"),
            r = [];
        return "IMG" === e.nodeName.toUpperCase() && e[o.ns] && e[o.ns].srcset && (t = e[o.ns].srcset), t && (r = o.getCandidatesFromSourceSet(t, n)), r
    }, o.backfaceVisibilityFix = function(e) {
        var t = e.style || {},
            n = "webkitBackfaceVisibility" in t,
            r = t.zoom;
        n && (t.zoom = ".999", n = e.offsetWidth, t.zoom = r)
    }, o.setIntrinsicSize = function() {
        var n = {},
            r = function(e, t, n) {
                t && e.setAttribute("width", parseInt(t / n, 10))
            };
        return function(i, s) {
            var u;
            i[o.ns] && !e.pfStopIntrinsicSize && (void 0 === i[o.ns].dims && (i[o.ns].dims = i.getAttribute("width") || i.getAttribute("height")), i[o.ns].dims || (s.url in n ? r(i, n[s.url], s.resolution) : (u = t.createElement("img"), u.onload = function() {
                if (n[s.url] = u.width, !n[s.url])
                    try {
                        t.body.appendChild(u), n[s.url] = u.width || u.offsetWidth, t.body.removeChild(u)
                    } catch (e) {}
                i.src === s.url && r(i, n[s.url], s.resolution), i = null, u.onload = null, u = null
            }, u.src = s.url)))
        }
    }(), o.applyBestCandidate = function(e, t) {
        var n,
            r,
            i;
        e.sort(o.ascendingSort), r = e.length, i = e[r - 1];
        for (var s = 0; r > s; s++)
            if (n = e[s], n.resolution >= o.getDpr()) {
                i = n;
                break
            }
        i && (i.url = o.makeUrl(i.url), t.src !== i.url && (o.restrictsMixedContent() && "http:" === i.url.substr(0, "http:".length).toLowerCase() ? void 0 !== window.console && console.warn("Blocked mixed content image " + i.url) : (t.src = i.url, t.currentSrc = t.src, o.backfaceVisibilityFix(t))), o.setIntrinsicSize(t, i))
    }, o.ascendingSort = function(e, t) {
        return e.resolution - t.resolution
    }, o.removeVideoShim = function(e) {
        var t = e.getElementsByTagName("video");
        if (t.length) {
            for (var n = t[0], r = n.getElementsByTagName("source"); r.length;)
                e.insertBefore(r[0], n);
            n.parentNode.removeChild(n)
        }
    }, o.getAllElements = function() {
        for (var e = [], n = t.getElementsByTagName("img"), r = 0, i = n.length; i > r; r++) {
            var s = n[r];
            ("PICTURE" === s.parentNode.nodeName.toUpperCase() || null !== s.getAttribute("srcset") || s[o.ns] && null !== s[o.ns].srcset) && e.push(s)
        }
        return e
    }, o.getMatch = function(e, t) {
        for (var n, r = t.childNodes, i = 0, s = r.length; s > i; i++) {
            var u = r[i];
            if (1 === u.nodeType) {
                if (u === e)
                    return n;
                if ("SOURCE" === u.nodeName.toUpperCase()) {
                    null !== u.getAttribute("src") && void 0 !== typeof console && console.warn("The `src` attribute is invalid on `picture` `source` element; instead, use `srcset`.");
                    var a = u.getAttribute("media");
                    if (u.getAttribute("srcset") && (!a || o.matchesMedia(a))) {
                        var f = o.verifyTypeSupport(u);
                        if (f === !0) {
                            n = u;
                            break
                        }
                        if ("pending" === f)
                            return !1
                    }
                }
            }
        }
        return n
    }, s(), i._ = o, r(i)
}(window, window.document, new window.Image), function() {
    var e = this,
        t = e._,
        n = {},
        r = Array.prototype,
        i = Object.prototype,
        s = Function.prototype,
        o = r.push,
        u = r.slice,
        a = r.concat,
        f = i.toString,
        l = i.hasOwnProperty,
        c = r.forEach,
        h = r.map,
        p = r.reduce,
        d = r.reduceRight,
        v = r.filter,
        m = r.every,
        g = r.some,
        y = r.indexOf,
        b = r.lastIndexOf,
        w = Array.isArray,
        E = Object.keys,
        S = s.bind,
        x = function(e) {
            return e instanceof x ? e : this instanceof x ? void (this._wrapped = e) : new x(e)
        };
    "undefined" != typeof exports ? ("undefined" != typeof module && module.exports && (exports = module.exports = x), exports._ = x) : e._ = x, x.VERSION = "1.6.0";
    var T = x.each = x.forEach = function(e, t, r) {
        if (null == e)
            return e;
        if (c && e.forEach === c)
            e.forEach(t, r);
        else if (e.length === +e.length) {
            for (var i = 0, s = e.length; s > i; i++)
                if (t.call(r, e[i], i, e) === n)
                    return
        } else
            for (var o = x.keys(e), i = 0, s = o.length; s > i; i++)
                if (t.call(r, e[o[i]], o[i], e) === n)
                    return;
        return e
    };
    x.map = x.collect = function(e, t, n) {
        var r = [];
        return null == e ? r : h && e.map === h ? e.map(t, n) : (T(e, function(e, i, s) {
            r.push(t.call(n, e, i, s))
        }), r)
    };
    var N = "Reduce of empty array with no initial value";
    x.reduce = x.foldl = x.inject = function(e, t, n, r) {
        var i = arguments.length > 2;
        if (null == e && (e = []), p && e.reduce === p)
            return r && (t = x.bind(t, r)), i ? e.reduce(t, n) : e.reduce(t);
        if (T(e, function(e, s, o) {
            i ? n = t.call(r, n, e, s, o) : (n = e, i = !0)
        }), !i)
            throw new TypeError(N);
        return n
    }, x.reduceRight = x.foldr = function(e, t, n, r) {
        var i = arguments.length > 2;
        if (null == e && (e = []), d && e.reduceRight === d)
            return r && (t = x.bind(t, r)), i ? e.reduceRight(t, n) : e.reduceRight(t);
        var s = e.length;
        if (s !== +s) {
            var o = x.keys(e);
            s = o.length
        }
        if (T(e, function(u, a, f) {
            a = o ? o[--s] : --s, i ? n = t.call(r, n, e[a], a, f) : (n = e[a], i = !0)
        }), !i)
            throw new TypeError(N);
        return n
    }, x.find = x.detect = function(e, t, n) {
        var r;
        return C(e, function(e, i, s) {
            return t.call(n, e, i, s) ? (r = e, !0) : void 0
        }), r
    }, x.filter = x.select = function(e, t, n) {
        var r = [];
        return null == e ? r : v && e.filter === v ? e.filter(t, n) : (T(e, function(e, i, s) {
            t.call(n, e, i, s) && r.push(e)
        }), r)
    }, x.reject = function(e, t, n) {
        return x.filter(e, function(e, r, i) {
            return !t.call(n, e, r, i)
        }, n)
    }, x.every = x.all = function(e, t, r) {
        t || (t = x.identity);
        var i = !0;
        return null == e ? i : m && e.every === m ? e.every(t, r) : (T(e, function(e, s, o) {
            return (i = i && t.call(r, e, s, o)) ? void 0 : n
        }), !!i)
    };
    var C = x.some = x.any = function(e, t, r) {
        t || (t = x.identity);
        var i = !1;
        return null == e ? i : g && e.some === g ? e.some(t, r) : (T(e, function(e, s, o) {
            return i || (i = t.call(r, e, s, o)) ? n : void 0
        }), !!i)
    };
    x.contains = x.include = function(e, t) {
        return null == e ? !1 : y && e.indexOf === y ? e.indexOf(t) != -1 : C(e, function(e) {
            return e === t
        })
    }, x.invoke = function(e, t) {
        var n = u.call(arguments, 2),
            r = x.isFunction(t);
        return x.map(e, function(e) {
            return (r ? t : e[t]).apply(e, n)
        })
    }, x.pluck = function(e, t) {
        return x.map(e, x.property(t))
    }, x.where = function(e, t) {
        return x.filter(e, x.matches(t))
    }, x.findWhere = function(e, t) {
        return x.find(e, x.matches(t))
    }, x.max = function(e, t, n) {
        if (!t && x.isArray(e) && e[0] === +e[0] && e.length < 65535)
            return Math.max.apply(Math, e);
        var r = -1 / 0,
            i = -1 / 0;
        return T(e, function(e, s, o) {
            var u = t ? t.call(n, e, s, o) : e;
            u > i && (r = e, i = u)
        }), r
    }, x.min = function(e, t, n) {
        if (!t && x.isArray(e) && e[0] === +e[0] && e.length < 65535)
            return Math.min.apply(Math, e);
        var r = 1 / 0,
            i = 1 / 0;
        return T(e, function(e, s, o) {
            var u = t ? t.call(n, e, s, o) : e;
            i > u && (r = e, i = u)
        }), r
    }, x.shuffle = function(e) {
        var t,
            n = 0,
            r = [];
        return T(e, function(e) {
            t = x.random(n++), r[n - 1] = r[t], r[t] = e
        }), r
    }, x.sample = function(e, t, n) {
        return null == t || n ? (e.length !== +e.length && (e = x.values(e)), e[x.random(e.length - 1)]) : x.shuffle(e).slice(0, Math.max(0, t))
    };
    var k = function(e) {
        return null == e ? x.identity : x.isFunction(e) ? e : x.property(e)
    };
    x.sortBy = function(e, t, n) {
        return t = k(t), x.pluck(x.map(e, function(e, r, i) {
            return {
                value: e,
                index: r,
                criteria: t.call(n, e, r, i)
            }
        }).sort(function(e, t) {
            var n = e.criteria,
                r = t.criteria;
            if (n !== r) {
                if (n > r || n === void 0)
                    return 1;
                if (r > n || r === void 0)
                    return -1
            }
            return e.index - t.index
        }), "value")
    };
    var L = function(e) {
        return function(t, n, r) {
            var i = {};
            return n = k(n), T(t, function(s, o) {
                var u = n.call(r, s, o, t);
                e(i, u, s)
            }), i
        }
    };
    x.groupBy = L(function(e, t, n) {
        x.has(e, t) ? e[t].push(n) : e[t] = [n]
    }), x.indexBy = L(function(e, t, n) {
        e[t] = n
    }), x.countBy = L(function(e, t) {
        x.has(e, t) ? e[t]++ : e[t] = 1
    }), x.sortedIndex = function(e, t, n, r) {
        n = k(n);
        for (var i = n.call(r, t), s = 0, o = e.length; o > s;) {
            var u = s + o >>> 1;
            n.call(r, e[u]) < i ? s = u + 1 : o = u
        }
        return s
    }, x.toArray = function(e) {
        return e ? x.isArray(e) ? u.call(e) : e.length === +e.length ? x.map(e, x.identity) : x.values(e) : []
    }, x.size = function(e) {
        return null == e ? 0 : e.length === +e.length ? e.length : x.keys(e).length
    }, x.first = x.head = x.take = function(e, t, n) {
        return null == e ? void 0 : null == t || n ? e[0] : 0 > t ? [] : u.call(e, 0, t)
    }, x.initial = function(e, t, n) {
        return u.call(e, 0, e.length - (null == t || n ? 1 : t))
    }, x.last = function(e, t, n) {
        return null == e ? void 0 : null == t || n ? e[e.length - 1] : u.call(e, Math.max(e.length - t, 0))
    }, x.rest = x.tail = x.drop = function(e, t, n) {
        return u.call(e, null == t || n ? 1 : t)
    }, x.compact = function(e) {
        return x.filter(e, x.identity)
    };
    var A = function(e, t, n) {
        return t && x.every(e, x.isArray) ? a.apply(n, e) : (T(e, function(e) {
            x.isArray(e) || x.isArguments(e) ? t ? o.apply(n, e) : A(e, t, n) : n.push(e)
        }), n)
    };
    x.flatten = function(e, t) {
        return A(e, t, [])
    }, x.without = function(e) {
        return x.difference(e, u.call(arguments, 1))
    }, x.partition = function(e, t) {
        var n = [],
            r = [];
        return T(e, function(e) {
            (t(e) ? n : r).push(e)
        }), [n, r]
    }, x.uniq = x.unique = function(e, t, n, r) {
        x.isFunction(t) && (r = n, n = t, t = !1);
        var i = n ? x.map(e, n, r) : e,
            s = [],
            o = [];
        return T(i, function(n, r) {
            (t ? r && o[o.length - 1] === n : x.contains(o, n)) || (o.push(n), s.push(e[r]))
        }), s
    }, x.union = function() {
        return x.uniq(x.flatten(arguments, !0))
    }, x.intersection = function(e) {
        var t = u.call(arguments, 1);
        return x.filter(x.uniq(e), function(e) {
            return x.every(t, function(t) {
                return x.contains(t, e)
            })
        })
    }, x.difference = function(e) {
        var t = a.apply(r, u.call(arguments, 1));
        return x.filter(e, function(e) {
            return !x.contains(t, e)
        })
    }, x.zip = function() {
        for (var e = x.max(x.pluck(arguments, "length").concat(0)), t = new Array(e), n = 0; e > n; n++)
            t[n] = x.pluck(arguments, "" + n);
        return t
    }, x.object = function(e, t) {
        if (null == e)
            return {};
        for (var n = {}, r = 0, i = e.length; i > r; r++)
            t ? n[e[r]] = t[r] : n[e[r][0]] = e[r][1];
        return n
    }, x.indexOf = function(e, t, n) {
        if (null == e)
            return -1;
        var r = 0,
            i = e.length;
        if (n) {
            if ("number" != typeof n)
                return r = x.sortedIndex(e, t), e[r] === t ? r : -1;
            r = 0 > n ? Math.max(0, i + n) : n
        }
        if (y && e.indexOf === y)
            return e.indexOf(t, n);
        for (; i > r; r++)
            if (e[r] === t)
                return r;
        return -1
    }, x.lastIndexOf = function(e, t, n) {
        if (null == e)
            return -1;
        var r = null != n;
        if (b && e.lastIndexOf === b)
            return r ? e.lastIndexOf(t, n) : e.lastIndexOf(t);
        for (var i = r ? n : e.length; i--;)
            if (e[i] === t)
                return i;
        return -1
    }, x.range = function(e, t, n) {
        arguments.length <= 1 && (t = e || 0, e = 0), n = arguments[2] || 1;
        for (var r = Math.max(Math.ceil((t - e) / n), 0), i = 0, s = new Array(r); r > i;)
            s[i++] = e, e += n;
        return s
    };
    var O = function() {};
    x.bind = function(e, t) {
        var n,
            r;
        if (S && e.bind === S)
            return S.apply(e, u.call(arguments, 1));
        if (!x.isFunction(e))
            throw new TypeError;
        return n = u.call(arguments, 2), r = function() {
            if (this instanceof r) {
                O.prototype = e.prototype;
                var i = new O;
                O.prototype = null;
                var s = e.apply(i, n.concat(u.call(arguments)));
                return Object(s) === s ? s : i
            }
            return e.apply(t, n.concat(u.call(arguments)))
        }
    }, x.partial = function(e) {
        var t = u.call(arguments, 1);
        return function() {
            for (var n = 0, r = t.slice(), i = 0, s = r.length; s > i; i++)
                r[i] === x && (r[i] = arguments[n++]);
            for (; n < arguments.length;)
                r.push(arguments[n++]);
            return e.apply(this, r)
        }
    }, x.bindAll = function(e) {
        var t = u.call(arguments, 1);
        if (0 === t.length)
            throw new Error("bindAll must be passed function names");
        return T(t, function(t) {
            e[t] = x.bind(e[t], e)
        }), e
    }, x.memoize = function(e, t) {
        var n = {};
        return t || (t = x.identity), function() {
            var r = t.apply(this, arguments);
            return x.has(n, r) ? n[r] : n[r] = e.apply(this, arguments)
        }
    }, x.delay = function(e, t) {
        var n = u.call(arguments, 2);
        return setTimeout(function() {
            return e.apply(null, n)
        }, t)
    }, x.defer = function(e) {
        return x.delay.apply(x, [e, 1].concat(u.call(arguments, 1)))
    }, x.throttle = function(e, t, n) {
        var r,
            i,
            s,
            o = null,
            u = 0;
        n || (n = {});
        var a = function() {
            u = n.leading === !1 ? 0 : x.now(), o = null, s = e.apply(r, i), r = i = null
        };
        return function() {
            var f = x.now();
            u || n.leading !== !1 || (u = f);
            var l = t - (f - u);
            return r = this, i = arguments, 0 >= l ? (clearTimeout(o), o = null, u = f, s = e.apply(r, i), r = i = null) : o || n.trailing === !1 || (o = setTimeout(a, l)), s
        }
    }, x.debounce = function(e, t, n) {
        var r,
            i,
            s,
            o,
            u,
            a = function() {
                var f = x.now() - o;
                t > f ? r = setTimeout(a, t - f) : (r = null, n || (u = e.apply(s, i), s = i = null))
            };
        return function() {
            s = this, i = arguments, o = x.now();
            var f = n && !r;
            return r || (r = setTimeout(a, t)), f && (u = e.apply(s, i), s = i = null), u
        }
    }, x.once = function(e) {
        var t,
            n = !1;
        return function() {
            return n ? t : (n = !0, t = e.apply(this, arguments), e = null, t)
        }
    }, x.wrap = function(e, t) {
        return x.partial(t, e)
    }, x.compose = function() {
        var e = arguments;
        return function() {
            for (var t = arguments, n = e.length - 1; n >= 0; n--)
                t = [e[n].apply(this, t)];
            return t[0]
        }
    }, x.after = function(e, t) {
        return function() {
            return --e < 1 ? t.apply(this, arguments) : void 0
        }
    }, x.keys = function(e) {
        if (!x.isObject(e))
            return [];
        if (E)
            return E(e);
        var t = [];
        for (var n in e)
            x.has(e, n) && t.push(n);
        return t
    }, x.values = function(e) {
        for (var t = x.keys(e), n = t.length, r = new Array(n), i = 0; n > i; i++)
            r[i] = e[t[i]];
        return r
    }, x.pairs = function(e) {
        for (var t = x.keys(e), n = t.length, r = new Array(n), i = 0; n > i; i++)
            r[i] = [t[i], e[t[i]]];
        return r
    }, x.invert = function(e) {
        for (var t = {}, n = x.keys(e), r = 0, i = n.length; i > r; r++)
            t[e[n[r]]] = n[r];
        return t
    }, x.functions = x.methods = function(e) {
        var t = [];
        for (var n in e)
            x.isFunction(e[n]) && t.push(n);
        return t.sort()
    }, x.extend = function(e) {
        return T(u.call(arguments, 1), function(t) {
            if (t)
                for (var n in t)
                    e[n] = t[n]
        }), e
    }, x.pick = function(e) {
        var t = {},
            n = a.apply(r, u.call(arguments, 1));
        return T(n, function(n) {
            n in e && (t[n] = e[n])
        }), t
    }, x.omit = function(e) {
        var t = {},
            n = a.apply(r, u.call(arguments, 1));
        for (var i in e)
            x.contains(n, i) || (t[i] = e[i]);
        return t
    }, x.defaults = function(e) {
        return T(u.call(arguments, 1), function(t) {
            if (t)
                for (var n in t)
                    e[n] === void 0 && (e[n] = t[n])
        }), e
    }, x.clone = function(e) {
        return x.isObject(e) ? x.isArray(e) ? e.slice() : x.extend({}, e) : e
    }, x.tap = function(e, t) {
        return t(e), e
    };
    var M = function(e, t, n, r) {
        if (e === t)
            return 0 !== e || 1 / e == 1 / t;
        if (null == e || null == t)
            return e === t;
        e instanceof x && (e = e._wrapped), t instanceof x && (t = t._wrapped);
        var i = f.call(e);
        if (i != f.call(t))
            return !1;
        switch (i) {
        case "[object String]":
            return e == String(t);
        case "[object Number]":
            return e != +e ? t != +t : 0 == e ? 1 / e == 1 / t : e == +t;
        case "[object Date]":
        case "[object Boolean]":
            return +e == +t;
        case "[object RegExp]":
            return e.source == t.source && e.global == t.global && e.multiline == t.multiline && e.ignoreCase == t.ignoreCase
        }
        if ("object" != typeof e || "object" != typeof t)
            return !1;
        for (var s = n.length; s--;)
            if (n[s] == e)
                return r[s] == t;
        var o = e.constructor,
            u = t.constructor;
        if (o !== u && !(x.isFunction(o) && o instanceof o && x.isFunction(u) && u instanceof u) && "constructor" in e && "constructor" in t)
            return !1;
        n.push(e), r.push(t);
        var a = 0,
            l = !0;
        if ("[object Array]" == i) {
            if (a = e.length, l = a == t.length)
                for (; a-- && (l = M(e[a], t[a], n, r));)
                    ;
        } else {
            for (var c in e)
                if (x.has(e, c) && (a++, !(l = x.has(t, c) && M(e[c], t[c], n, r))))
                    break;
            if (l) {
                for (c in t)
                    if (x.has(t, c) && !(a--))
                        break;
                l = !a
            }
        }
        return n.pop(), r.pop(), l
    };
    x.isEqual = function(e, t) {
        return M(e, t, [], [])
    }, x.isEmpty = function(e) {
        if (null == e)
            return !0;
        if (x.isArray(e) || x.isString(e))
            return 0 === e.length;
        for (var t in e)
            if (x.has(e, t))
                return !1;
        return !0
    }, x.isElement = function(e) {
        return !!e && 1 === e.nodeType
    }, x.isArray = w || function(e) {
        return "[object Array]" == f.call(e)
    }, x.isObject = function(e) {
        return e === Object(e)
    }, T(["Arguments", "Function", "String", "Number", "Date", "RegExp"], function(e) {
        x["is" + e] = function(t) {
            return f.call(t) == "[object " + e + "]"
        }
    }), x.isArguments(arguments) || (x.isArguments = function(e) {
        return !!e && !!x.has(e, "callee")
    }), "function" != typeof /./ && (x.isFunction = function(e) {
        return "function" == typeof e
    }), x.isFinite = function(e) {
        return isFinite(e) && !isNaN(parseFloat(e))
    }, x.isNaN = function(e) {
        return x.isNumber(e) && e != +e
    }, x.isBoolean = function(e) {
        return e === !0 || e === !1 || "[object Boolean]" == f.call(e)
    }, x.isNull = function(e) {
        return null === e
    }, x.isUndefined = function(e) {
        return e === void 0
    }, x.has = function(e, t) {
        return l.call(e, t)
    }, x.noConflict = function() {
        return e._ = t, this
    }, x.identity = function(e) {
        return e
    }, x.constant = function(e) {
        return function() {
            return e
        }
    }, x.property = function(e) {
        return function(t) {
            return t[e]
        }
    }, x.matches = function(e) {
        return function(t) {
            if (t === e)
                return !0;
            for (var n in e)
                if (e[n] !== t[n])
                    return !1;
            return !0
        }
    }, x.times = function(e, t, n) {
        for (var r = Array(Math.max(0, e)), i = 0; e > i; i++)
            r[i] = t.call(n, i);
        return r
    }, x.random = function(e, t) {
        return null == t && (t = e, e = 0), e + Math.floor(Math.random() * (t - e + 1))
    }, x.now = Date.now || function() {
        return (new Date).getTime()
    };
    var _ = {
        escape: {
            "&": "&amp;",
            "<": "&lt;",
            ">": "&gt;",
            '"': "&quot;",
            "'": "&#x27;"
        }
    };
    _.unescape = x.invert(_.escape);
    var D = {
        escape: new RegExp("[" + x.keys(_.escape).join("") + "]", "g"),
        unescape: new RegExp("(" + x.keys(_.unescape).join("|") + ")", "g")
    };
    x.each(["escape", "unescape"], function(e) {
        x[e] = function(t) {
            return null == t ? "" : ("" + t).replace(D[e], function(t) {
                return _[e][t]
            })
        }
    }), x.result = function(e, t) {
        if (null == e)
            return void 0;
        var n = e[t];
        return x.isFunction(n) ? n.call(e) : n
    }, x.mixin = function(e) {
        T(x.functions(e), function(t) {
            var n = x[t] = e[t];
            x.prototype[t] = function() {
                var e = [this._wrapped];
                return o.apply(e, arguments), F.call(this, n.apply(x, e))
            }
        })
    };
    var P = 0;
    x.uniqueId = function(e) {
        var t = ++P + "";
        return e ? e + t : t
    }, x.templateSettings = {
        evaluate: /<%([\s\S]+?)%>/g,
        interpolate: /<%=([\s\S]+?)%>/g,
        escape: /<%-([\s\S]+?)%>/g
    };
    var H = /(.)^/,
        B = {
            "'": "'",
            "\\": "\\",
            "\r": "r",
            "\n": "n",
            "	": "t",
            "\u2028": "u2028",
            "\u2029": "u2029"
        },
        j = /\\|'|\r|\n|\t|\u2028|\u2029/g;
    x.template = function(e, t, n) {
        var r;
        n = x.defaults({}, n, x.templateSettings);
        var i = new RegExp([(n.escape || H).source, (n.interpolate || H).source, (n.evaluate || H).source].join("|") + "|$", "g"),
            s = 0,
            o = "__p+='";
        e.replace(i, function(t, n, r, i, u) {
            return o += e.slice(s, u).replace(j, function(e) {
                return "\\" + B[e]
            }), n && (o += "'+\n((__t=(" + n + "))==null?'':_.escape(__t))+\n'"), r && (o += "'+\n((__t=(" + r + "))==null?'':__t)+\n'"), i && (o += "';\n" + i + "\n__p+='"), s = u + t.length, t
        }), o += "';\n", n.variable || (o = "with(obj||{}){\n" + o + "}\n"), o = "var __t,__p='',__j=Array.prototype.join,print=function(){__p+=__j.call(arguments,'');};\n" + o + "return __p;\n";
        try {
            r = new Function(n.variable || "obj", "_", o)
        } catch (u) {
            throw u.source = o, u
        }
        if (t)
            return r(t, x);
        var a = function(e) {
            return r.call(this, e, x)
        };
        return a.source = "function(" + (n.variable || "obj") + "){\n" + o + "}", a
    }, x.chain = function(e) {
        return x(e).chain()
    };
    var F = function(e) {
        return this._chain ? x(e).chain() : e
    };
    x.mixin(x), T(["pop", "push", "reverse", "shift", "sort", "splice", "unshift"], function(e) {
        var t = r[e];
        x.prototype[e] = function() {
            var n = this._wrapped;
            return t.apply(n, arguments), "shift" != e && "splice" != e || 0 !== n.length || delete n[0], F.call(this, n)
        }
    }), T(["concat", "join", "slice"], function(e) {
        var t = r[e];
        x.prototype[e] = function() {
            return F.call(this, t.apply(this._wrapped, arguments))
        }
    }), x.extend(x.prototype, {
        chain: function() {
            return this._chain = !0, this
        },
        value: function() {
            return this._wrapped
        }
    }), "function" == typeof define && define.amd && define("underscore", [], function() {
        return x
    })
}.call(this), !function(e) {
    "function" == typeof define && define.amd ? define("jquery_mousewheel", ["jquery"], e) : "object" == typeof exports ? module.exports = e : e(jQuery)
}(function(e) {
    function t(t) {
        var o = t || window.event,
            u = a.call(arguments, 1),
            f = 0,
            h = 0,
            p = 0,
            v = 0,
            m = 0,
            g = 0;
        if (t = e.event.fix(o), t.type = "mousewheel", "detail" in o && (p = -1 * o.detail), "wheelDelta" in o && (p = o.wheelDelta), "wheelDeltaY" in o && (p = o.wheelDeltaY), "wheelDeltaX" in o && (h = -1 * o.wheelDeltaX), "axis" in o && o.axis === o.HORIZONTAL_AXIS && (h = -1 * p, p = 0), f = 0 === p ? h : p, "deltaY" in o && (p = -1 * o.deltaY, f = p), "deltaX" in o && (h = o.deltaX, 0 === p && (f = -1 * h)), 0 !== p || 0 !== h) {
            if (1 === o.deltaMode) {
                var y = e.data(this, "mousewheel-line-height");
                f *= y, p *= y, h *= y
            } else if (2 === o.deltaMode) {
                var b = e.data(this, "mousewheel-page-height");
                f *= b, p *= b, h *= b
            }
            if (v = Math.max(Math.abs(p), Math.abs(h)), (!s || s > v) && (s = v, r(o, v) && (s /= 40)), r(o, v) && (f /= 40, h /= 40, p /= 40), f = Math[f >= 1 ? "floor" : "ceil"](f / s), h = Math[h >= 1 ? "floor" : "ceil"](h / s), p = Math[p >= 1 ? "floor" : "ceil"](p / s), l.settings.normalizeOffset && this.getBoundingClientRect) {
                var w = this.getBoundingClientRect();
                m = t.clientX - w.left, g = t.clientY - w.top
            }
            return t.deltaX = h, t.deltaY = p, t.deltaFactor = s, t.offsetX = m, t.offsetY = g, t.deltaMode = 0, u.unshift(t, f, h, p), i && clearTimeout(i), i = setTimeout(n, 200), (e.event.dispatch || e.event.handle).apply(this, u)
        }
    }
    function n() {
        s = null
    }
    function r(e, t) {
        return l.settings.adjustOldDeltas && "mousewheel" === e.type && t % 120 === 0
    }
    var i,
        s,
        o = ["wheel", "mousewheel", "DOMMouseScroll", "MozMousePixelScroll"],
        u = "onwheel" in document || document.documentMode >= 9 ? ["wheel"] : ["mousewheel", "DomMouseScroll", "MozMousePixelScroll"],
        a = Array.prototype.slice;
    if (e.event.fixHooks)
        for (var f = o.length; f;)
            e.event.fixHooks[o[--f]] = e.event.mouseHooks;
    var l = e.event.special.mousewheel = {
        version: "3.1.12",
        setup: function() {
            if (this.addEventListener)
                for (var n = u.length; n;)
                    this.addEventListener(u[--n], t, !1);
            else
                this.onmousewheel = t;
            e.data(this, "mousewheel-line-height", l.getLineHeight(this)), e.data(this, "mousewheel-page-height", l.getPageHeight(this))
        },
        teardown: function() {
            if (this.removeEventListener)
                for (var n = u.length; n;)
                    this.removeEventListener(u[--n], t, !1);
            else
                this.onmousewheel = null;
            e.removeData(this, "mousewheel-line-height"), e.removeData(this, "mousewheel-page-height")
        },
        getLineHeight: function(t) {
            var n = e(t),
                r = n["offsetParent" in e.fn ? "offsetParent" : "parent"]();
            return r.length || (r = e("body")), parseInt(r.css("fontSize"), 10) || parseInt(n.css("fontSize"), 10) || 16
        },
        getPageHeight: function(t) {
            return e(t).height()
        },
        settings: {
            adjustOldDeltas: !0,
            normalizeOffset: !0
        }
    };
    e.fn.extend({
        mousewheel: function(e) {
            return e ? this.bind("mousewheel", e) : this.trigger("mousewheel")
        },
        unmousewheel: function(e) {
            return this.unbind("mousewheel", e)
        }
    })
}), function() {
    var e = 0,
        t = ["webkit", "moz"];
    for (var n = 0; n < t.length && !window.requestAnimationFrame; ++n)
        window.requestAnimationFrame = window[t[n] + "RequestAnimationFrame"], window.cancelAnimationFrame = window[t[n] + "CancelAnimationFrame"] || window[t[n] + "CancelRequestAnimationFrame"];
    window.requestAnimationFrame || (window.requestAnimationFrame = function(t, n) {
        var r = (new Date).getTime(),
            i = Math.max(0, 16 - (r - e)),
            s = window.setTimeout(function() {
                t(r + i)
            }, i);
        return e = r + i, s
    }), window.cancelAnimationFrame || (window.cancelAnimationFrame = function(e) {
        clearTimeout(e)
    })
}(), define("frontend/rafpolyfill", function() {}), define("frontend/globals", ["jquery", "underscore", "jquery_mousewheel", "frontend/rafpolyfill"], function(e, t, n, r) {
    var i = function(n) {
            var r = this,
                i,
                s,
                o,
                u,
                a,
                f,
                l,
                c,
                h;
            i = {
                use_mousewheel: !0,
                raf_scrolling: !0
            }, s = {
                scroll_top: 0,
                raf_is_ticking: !1,
                is_wheeling: !1,
                is_wheeling_timeout: null
            }, o = {
                document: e(document),
                window: e(window),
                html: e("html"),
                body: e("body"),
                scroll_target: e(document),
                scroll_receiver: e("html, body"),
                header: e(".js-header"),
                metanav: e(".js-metanav"),
                pulltab: e(".js-pulltab"),
                pulltab_bg: e(".js-pulltab rect.bg")
            }, u = {
                iscroll: null
            }, a = {
                accent_color: "#009dff",
                modal_speed: 300,
                hover_speed: 200,
                tablet_max_width: 1015,
                phone_max_width: 767,
                share_image_url: null
            }, f = {
                can_touch: "ontouchstart" in window || "onmsgesturechange" in window ? !0 : !1,
                can_translate3d: function() {
                    var e = document.createElement("p"),
                        t,
                        n = {
                            webkitTransform: "-webkit-transform",
                            OTransform: "-o-transform",
                            msTransform: "-ms-transform",
                            MozTransform: "-moz-transform",
                            transform: "transform"
                        };
                    document.body.insertBefore(e, null);
                    for (var r in n)
                        n.hasOwnProperty(r) && e.style[r] !== undefined && (e.style[r] = "translate3d(1px,1px,1px)", t = window.getComputedStyle(e).getPropertyValue(n[r]));
                    return document.body.removeChild(e), t !== undefined && t.length > 0 && t !== "none"
                }(),
                supports_passive_events: function() {
                    var e = !1;
                    try {
                        var t = Object.defineProperty({}, "passive", {
                            get: function() {
                                e = !0
                            }
                        });
                        window.addEventListener("test", null, t)
                    } catch (n) {}
                    return e
                }()
            }, c = {
                init: function() {
                    f.can_touch && o.body.addClass("feature-touch"), o.window.on("resize", function() {
                        o.document.trigger({
                            type: "resize_simple",
                            win_width: o.window.width(),
                            win_height: o.window.height()
                        })
                    }), o.window.on("resize", t.debounce(function() {
                        o.document.trigger({
                            type: "resize_debounced",
                            win_width: o.window.width(),
                            win_height: o.window.height()
                        })
                    }, 300)), s.scroll_top = window.pageYOffset || o.body.scrollTop(), i.use_mousewheel && o.scroll_target[0].addEventListener("mousewheel", function() {
                        s.is_wheeling || (s.is_wheeling = !0), clearTimeout(s.is_wheeling_timeout), s.is_wheeling_timeout = setTimeout(function() {
                            s.is_wheeling = !1
                        }, 100), c._scroll_or_mousewheel_event()
                    }, f.supports_passive_events ? {
                        passive: !0
                    } : !1), o.scroll_target[0].addEventListener("scroll", function() {
                        s.is_wheeling || c._scroll_or_mousewheel_event()
                    }, f.supports_passive_events ? {
                        passive: !0
                    } : !1), c.simulate_links(), c.setup_hanging_punctuation(e(".box h1 > span, .box .dek"))
                },
                _scroll_or_mousewheel_event: function() {
                    i.raf_scrolling && !s.raf_is_ticking ? (requestAnimationFrame(c._trigger_scroll_event), s.raf_is_ticking = !0) : c._trigger_scroll_event()
                },
                _trigger_scroll_event: function() {
                    s.raf_is_ticking = !1;
                    var e = window.pageYOffset,
                        t = e ? e : o.body.scrollTop();
                    s.scroll_top != t && (s.scroll_top = t, o.document.trigger({
                        type: "scroll_simple",
                        scroll_top: s.scroll_top
                    }))
                },
                get_scroll_position: function() {
                    return s.scroll_top
                },
                set_scroll_position: function(e, t) {
                    o.scroll_receiver.animate({
                        scrollTop: e
                    }, {
                        duration: t ? 300 : 0,
                        easing: "easeInOutCubic"
                    })
                },
                set_share_image_url: function(e) {
                    r.properties.share_image_url = e
                },
                simulate_links: function() {
                    e("[data-simulated-link]").off("click.simulated_link").on("click.simulated_link", function(t) {
                        var n,
                            r;
                        n = e(this), r = n.data("simulated-link"), r && (t.preventDefault(), t.stopPropagation(), window.open && t.metaKey ? window.open(r, "_blank") : window.location.assign(r))
                    })
                },
                get_cookie: function(e) {
                    var t = e + "=",
                        n = document.cookie.split(";");
                    for (var r = 0; r < n.length; r++) {
                        var i = n[r].trim();
                        if (i.indexOf(t) === 0)
                            return i.substring(t.length, i.length)
                    }
                    return ""
                },
                setup_hanging_punctuation: function(t) {
                    t.each(function(t) {
                        var n = e(this),
                            r = n.html(),
                            i = r.slice(0, 1);
                        if (/(\u0022|\u201C|\u2018)/g.test(i)) {
                            n.html('<span class="hangpunc">' + i + "</span>" + r.slice(1));
                            var s = n.find(".hangpunc"),
                                o = n.is("h1, h2") ? 1 : .85;
                            s.css({
                                "margin-left": -1 * s.width() * o
                            })
                        }
                    })
                }
            }, l = {
                reflow: function(e) {
                    e || (e = 100);
                    var t = setTimeout(function() {
                        o.body.css("display", "none"), o.window.scrollTop(), o.body.css("display", "")
                    }, e)
                },
                once_visible: function(e, t) {
                    function s() {
                        e.is(":visible") || i > n ? t() : setTimeout(s, r), i++, r += 5
                    }
                    var n = 60,
                        r = 25,
                        i = 0;
                    s()
                },
                hex_to_rgb: function(e) {
                    var t = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(e);
                    return t ? [parseInt(t[1], 16), parseInt(t[2], 16), parseInt(t[3], 16)] : null
                }
            }, this.elements = o, this.objects = u, this.properties = a, this.features = f, this.fn = c, this.analytics_fn = h, this.helpers = l, c.init()
        },
        s = null;
    return function() {
        return s || (s = new i), s
    }
}), function(e) {
    "function" == typeof define && define.amd ? define("jquery_easing", ["jquery"], e) : e(jQuery)
}(function(e) {
    var t = "ui-effects-",
        n = e;
    e.effects = {
        effect: {}
    }, function(e, t) {
        function n(e, t, n) {
            var r = c[t.type] || {};
            return null == e ? n || !t.def ? null : t.def : (e = r.floor ? ~~e : parseFloat(e), isNaN(e) ? t.def : r.mod ? (e + r.mod) % r.mod : 0 > e ? 0 : e > r.max ? r.max : e)
        }
        function r(n) {
            var r = f(),
                i = r._rgba = [];
            return n = n.toLowerCase(), d(a, function(e, s) {
                var o,
                    u = s.re.exec(n),
                    a = u && s.parse(u),
                    f = s.space || "rgba";
                return a ? (o = r[f](a), r[l[f].cache] = o[l[f].cache], i = r._rgba = o._rgba, !1) : t
            }), i.length ? ("0,0,0,0" === i.join() && e.extend(i, s.transparent), r) : s[n]
        }
        function i(e, t, n) {
            return n = (n + 1) % 1, 1 > 6 * n ? e + 6 * (t - e) * n : 1 > 2 * n ? t : 2 > 3 * n ? e + 6 * (t - e) * (2 / 3 - n) : e
        }
        var s,
            o = "backgroundColor borderBottomColor borderLeftColor borderRightColor borderTopColor color columnRuleColor outlineColor textDecorationColor textEmphasisColor",
            u = /^([\-+])=\s*(\d+\.?\d*)/,
            a = [{
                re: /rgba?\(\s*(\d{1,3})\s*,\s*(\d{1,3})\s*,\s*(\d{1,3})\s*(?:,\s*(\d?(?:\.\d+)?)\s*)?\)/,
                parse: function(e) {
                    return [e[1], e[2], e[3], e[4]]
                }
            }, {
                re: /rgba?\(\s*(\d+(?:\.\d+)?)\%\s*,\s*(\d+(?:\.\d+)?)\%\s*,\s*(\d+(?:\.\d+)?)\%\s*(?:,\s*(\d?(?:\.\d+)?)\s*)?\)/,
                parse: function(e) {
                    return [2.55 * e[1], 2.55 * e[2], 2.55 * e[3], e[4]]
                }
            }, {
                re: /#([a-f0-9]{2})([a-f0-9]{2})([a-f0-9]{2})/,
                parse: function(e) {
                    return [parseInt(e[1], 16), parseInt(e[2], 16), parseInt(e[3], 16)]
                }
            }, {
                re: /#([a-f0-9])([a-f0-9])([a-f0-9])/,
                parse: function(e) {
                    return [parseInt(e[1] + e[1], 16), parseInt(e[2] + e[2], 16), parseInt(e[3] + e[3], 16)]
                }
            }, {
                re: /hsla?\(\s*(\d+(?:\.\d+)?)\s*,\s*(\d+(?:\.\d+)?)\%\s*,\s*(\d+(?:\.\d+)?)\%\s*(?:,\s*(\d?(?:\.\d+)?)\s*)?\)/,
                space: "hsla",
                parse: function(e) {
                    return [e[1], e[2] / 100, e[3] / 100, e[4]]
                }
            }],
            f = e.Color = function(t, n, r, i) {
                return new e.Color.fn.parse(t, n, r, i)
            },
            l = {
                rgba: {
                    props: {
                        red: {
                            idx: 0,
                            type: "byte"
                        },
                        green: {
                            idx: 1,
                            type: "byte"
                        },
                        blue: {
                            idx: 2,
                            type: "byte"
                        }
                    }
                },
                hsla: {
                    props: {
                        hue: {
                            idx: 0,
                            type: "degrees"
                        },
                        saturation: {
                            idx: 1,
                            type: "percent"
                        },
                        lightness: {
                            idx: 2,
                            type: "percent"
                        }
                    }
                }
            },
            c = {
                "byte": {
                    floor: !0,
                    max: 255
                },
                percent: {
                    max: 1
                },
                degrees: {
                    mod: 360,
                    floor: !0
                }
            },
            h = f.support = {},
            p = e("<p>")[0],
            d = e.each;
        p.style.cssText = "background-color:rgba(1,1,1,.5)", h.rgba = p.style.backgroundColor.indexOf("rgba") > -1, d(l, function(e, t) {
            t.cache = "_" + e, t.props.alpha = {
                idx: 3,
                type: "percent",
                def: 1
            }
        }), f.fn = e.extend(f.prototype, {
            parse: function(i, o, u, a) {
                if (i === t)
                    return this._rgba = [null, null, null, null], this;
                (i.jquery || i.nodeType) && (i = e(i).css(o), o = t);
                var c = this,
                    h = e.type(i),
                    p = this._rgba = [];
                return o !== t && (i = [i, o, u, a], h = "array"), "string" === h ? this.parse(r(i) || s._default) : "array" === h ? (d(l.rgba.props, function(e, t) {
                    p[t.idx] = n(i[t.idx], t)
                }), this) : "object" === h ? (i instanceof f ? d(l, function(e, t) {
                    i[t.cache] && (c[t.cache] = i[t.cache].slice())
                }) : d(l, function(t, r) {
                    var s = r.cache;
                    d(r.props, function(e, t) {
                        if (!c[s] && r.to) {
                            if ("alpha" === e || null == i[e])
                                return;
                            c[s] = r.to(c._rgba)
                        }
                        c[s][t.idx] = n(i[e], t, !0)
                    }), c[s] && 0 > e.inArray(null, c[s].slice(0, 3)) && (c[s][3] = 1, r.from && (c._rgba = r.from(c[s])))
                }), this) : t
            },
            is: function(e) {
                var n = f(e),
                    r = !0,
                    i = this;
                return d(l, function(e, s) {
                    var o,
                        u = n[s.cache];
                    return u && (o = i[s.cache] || s.to && s.to(i._rgba) || [], d(s.props, function(e, n) {
                        return null != u[n.idx] ? r = u[n.idx] === o[n.idx] : t
                    })), r
                }), r
            },
            _space: function() {
                var e = [],
                    t = this;
                return d(l, function(n, r) {
                    t[r.cache] && e.push(n)
                }), e.pop()
            },
            transition: function(e, t) {
                var r = f(e),
                    i = r._space(),
                    s = l[i],
                    o = 0 === this.alpha() ? f("transparent") : this,
                    u = o[s.cache] || s.to(o._rgba),
                    a = u.slice();
                return r = r[s.cache], d(s.props, function(e, i) {
                    var s = i.idx,
                        o = u[s],
                        f = r[s],
                        l = c[i.type] || {};
                    null !== f && (null === o ? a[s] = f : (l.mod && (f - o > l.mod / 2 ? o += l.mod : o - f > l.mod / 2 && (o -= l.mod)), a[s] = n((f - o) * t + o, i)))
                }), this[i](a)
            },
            blend: function(t) {
                if (1 === this._rgba[3])
                    return this;
                var n = this._rgba.slice(),
                    r = n.pop(),
                    i = f(t)._rgba;
                return f(e.map(n, function(e, t) {
                    return (1 - r) * i[t] + r * e
                }))
            },
            toRgbaString: function() {
                var t = "rgba(",
                    n = e.map(this._rgba, function(e, t) {
                        return null == e ? t > 2 ? 1 : 0 : e
                    });
                return 1 === n[3] && (n.pop(), t = "rgb("), t + n.join() + ")"
            },
            toHslaString: function() {
                var t = "hsla(",
                    n = e.map(this.hsla(), function(e, t) {
                        return null == e && (e = t > 2 ? 1 : 0), t && 3 > t && (e = Math.round(100 * e) + "%"), e
                    });
                return 1 === n[3] && (n.pop(), t = "hsl("), t + n.join() + ")"
            },
            toHexString: function(t) {
                var n = this._rgba.slice(),
                    r = n.pop();
                return t && n.push(~~(255 * r)), "#" + e.map(n, function(e) {
                    return e = (e || 0).toString(16), 1 === e.length ? "0" + e : e
                }).join("")
            },
            toString: function() {
                return 0 === this._rgba[3] ? "transparent" : this.toRgbaString()
            }
        }), f.fn.parse.prototype = f.fn, l.hsla.to = function(e) {
            if (null == e[0] || null == e[1] || null == e[2])
                return [null, null, null, e[3]];
            var t,
                n,
                r = e[0] / 255,
                i = e[1] / 255,
                s = e[2] / 255,
                o = e[3],
                u = Math.max(r, i, s),
                a = Math.min(r, i, s),
                f = u - a,
                l = u + a,
                c = .5 * l;
            return t = a === u ? 0 : r === u ? 60 * (i - s) / f + 360 : i === u ? 60 * (s - r) / f + 120 : 60 * (r - i) / f + 240, n = 0 === f ? 0 : .5 >= c ? f / l : f / (2 - l), [Math.round(t) % 360, n, c, null == o ? 1 : o]
        }, l.hsla.from = function(e) {
            if (null == e[0] || null == e[1] || null == e[2])
                return [null, null, null, e[3]];
            var t = e[0] / 360,
                n = e[1],
                r = e[2],
                s = e[3],
                o = .5 >= r ? r * (1 + n) : r + n - r * n,
                u = 2 * r - o;
            return [Math.round(255 * i(u, o, t + 1 / 3)), Math.round(255 * i(u, o, t)), Math.round(255 * i(u, o, t - 1 / 3)), s]
        }, d(l, function(r, i) {
            var s = i.props,
                o = i.cache,
                a = i.to,
                l = i.from;
            f.fn[r] = function(r) {
                if (a && !this[o] && (this[o] = a(this._rgba)), r === t)
                    return this[o].slice();
                var i,
                    u = e.type(r),
                    c = "array" === u || "object" === u ? r : arguments,
                    h = this[o].slice();
                return d(s, function(e, t) {
                    var r = c["object" === u ? e : t.idx];
                    null == r && (r = h[t.idx]), h[t.idx] = n(r, t)
                }), l ? (i = f(l(h)), i[o] = h, i) : f(h)
            }, d(s, function(t, n) {
                f.fn[t] || (f.fn[t] = function(i) {
                    var s,
                        o = e.type(i),
                        a = "alpha" === t ? this._hsla ? "hsla" : "rgba" : r,
                        f = this[a](),
                        l = f[n.idx];
                    return "undefined" === o ? l : ("function" === o && (i = i.call(this, l), o = e.type(i)), null == i && n.empty ? this : ("string" === o && (s = u.exec(i), s && (i = l + parseFloat(s[2]) * ("+" === s[1] ? 1 : -1))), f[n.idx] = i, this[a](f)))
                })
            })
        }), f.hook = function(t) {
            var n = t.split(" ");
            d(n, function(t, n) {
                e.cssHooks[n] = {
                    set: function(t, i) {
                        var s,
                            o,
                            u = "";
                        if ("transparent" !== i && ("string" !== e.type(i) || (s = r(i)))) {
                            if (i = f(s || i), !h.rgba && 1 !== i._rgba[3]) {
                                for (o = "backgroundColor" === n ? t.parentNode : t; ("" === u || "transparent" === u) && o && o.style;)
                                    try {
                                        u = e.css(o, "backgroundColor"), o = o.parentNode
                                    } catch (a) {}
                                i = i.blend(u && "transparent" !== u ? u : "_default")
                            }
                            i = i.toRgbaString()
                        }
                        try {
                            t.style[n] = i
                        } catch (a) {}
                    }
                }, e.fx.step[n] = function(t) {
                    t.colorInit || (t.start = f(t.elem, n), t.end = f(t.end), t.colorInit = !0), e.cssHooks[n].set(t.elem, t.start.transition(t.end, t.pos))
                }
            })
        }, f.hook(o), e.cssHooks.borderColor = {
            expand: function(e) {
                var t = {};
                return d(["Top", "Right", "Bottom", "Left"], function(n, r) {
                    t["border" + r + "Color"] = e
                }), t
            }
        }, s = e.Color.names = {
            aqua: "#00ffff",
            black: "#000000",
            blue: "#0000ff",
            fuchsia: "#ff00ff",
            gray: "#808080",
            green: "#008000",
            lime: "#00ff00",
            maroon: "#800000",
            navy: "#000080",
            olive: "#808000",
            purple: "#800080",
            red: "#ff0000",
            silver: "#c0c0c0",
            teal: "#008080",
            white: "#ffffff",
            yellow: "#ffff00",
            transparent: [null, null, null, 0],
            _default: "#ffffff"
        }
    }(n), function() {
        function t(t) {
            var n,
                r,
                i = t.ownerDocument.defaultView ? t.ownerDocument.defaultView.getComputedStyle(t, null) : t.currentStyle,
                s = {};
            if (i && i.length && i[0] && i[i[0]])
                for (r = i.length; r--;)
                    n = i[r], "string" == typeof i[n] && (s[e.camelCase(n)] = i[n]);
            else
                for (n in i)
                    "string" == typeof i[n] && (s[n] = i[n]);
            return s
        }
        function r(t, n) {
            var r,
                i,
                s = {};
            for (r in n)
                i = n[r], t[r] !== i && (o[r] || (e.fx.step[r] || !isNaN(parseFloat(i))) && (s[r] = i));
            return s
        }
        var s = ["add", "remove", "toggle"],
            o = {
                border: 1,
                borderBottom: 1,
                borderColor: 1,
                borderLeft: 1,
                borderRight: 1,
                borderTop: 1,
                borderWidth: 1,
                margin: 1,
                padding: 1
            };
        e.each(["borderLeftStyle", "borderRightStyle", "borderBottomStyle", "borderTopStyle"], function(t, r) {
            e.fx.step[r] = function(e) {
                ("none" !== e.end && !e.setAttr || 1 === e.pos && !e.setAttr) && (n.style(e.elem, r, e.end), e.setAttr = !0)
            }
        }), e.fn.addBack || (e.fn.addBack = function(e) {
            return this.add(null == e ? this.prevObject : this.prevObject.filter(e))
        }), e.effects.animateClass = function(n, i, o, u) {
            var a = e.speed(i, o, u);
            return this.queue(function() {
                var i,
                    o = e(this),
                    u = o.attr("class") || "",
                    f = a.children ? o.find("*").addBack() : o;
                f = f.map(function() {
                    var n = e(this);
                    return {
                        el: n,
                        start: t(this)
                    }
                }), i = function() {
                    e.each(s, function(e, t) {
                        n[t] && o[t + "Class"](n[t])
                    })
                }, i(), f = f.map(function() {
                    return this.end = t(this.el[0]), this.diff = r(this.start, this.end), this
                }), o.attr("class", u), f = f.map(function() {
                    var t = this,
                        n = e.Deferred(),
                        r = e.extend({}, a, {
                            queue: !1,
                            complete: function() {
                                n.resolve(t)
                            }
                        });
                    return this.el.animate(this.diff, r), n.promise()
                }), e.when.apply(e, f.get()).done(function() {
                    i(), e.each(arguments, function() {
                        var t = this.el;
                        e.each(this.diff, function(e) {
                            t.css(e, "")
                        })
                    }), a.complete.call(o[0])
                })
            })
        }, e.fn.extend({
            addClass: function(t) {
                return function(n, r, i, s) {
                    return r ? e.effects.animateClass.call(this, {
                        add: n
                    }, r, i, s) : t.apply(this, arguments)
                }
            }(e.fn.addClass),
            removeClass: function(t) {
                return function(n, r, i, s) {
                    return arguments.length > 1 ? e.effects.animateClass.call(this, {
                        remove: n
                    }, r, i, s) : t.apply(this, arguments)
                }
            }(e.fn.removeClass),
            toggleClass: function(t) {
                return function(n, r, i, s, o) {
                    return "boolean" == typeof r || void 0 === r ? i ? e.effects.animateClass.call(this, r ? {
                        add: n
                    } : {
                        remove: n
                    }, i, s, o) : t.apply(this, arguments) : e.effects.animateClass.call(this, {
                        toggle: n
                    }, r, i, s)
                }
            }(e.fn.toggleClass),
            switchClass: function(t, n, r, i, s) {
                return e.effects.animateClass.call(this, {
                    add: n,
                    remove: t
                }, r, i, s)
            }
        })
    }(), function() {
        function n(t, n, r, i) {
            return e.isPlainObject(t) && (n = t, t = t.effect), t = {
                effect: t
            }, null == n && (n = {}), e.isFunction(n) && (i = n, r = null, n = {}), ("number" == typeof n || e.fx.speeds[n]) && (i = r, r = n, n = {}), e.isFunction(r) && (i = r, r = null), n && e.extend(t, n), r = r || n.duration, t.duration = e.fx.off ? 0 : "number" == typeof r ? r : r in e.fx.speeds ? e.fx.speeds[r] : e.fx.speeds._default, t.complete = i || n.complete, t
        }
        function r(t) {
            return !t || "number" == typeof t || e.fx.speeds[t] ? !0 : "string" != typeof t || e.effects.effect[t] ? e.isFunction(t) ? !0 : "object" != typeof t || t.effect ? !1 : !0 : !0
        }
        e.extend(e.effects, {
            version: "1.11.4",
            save: function(e, n) {
                for (var r = 0; n.length > r; r++)
                    null !== n[r] && e.data(t + n[r], e[0].style[n[r]])
            },
            restore: function(e, n) {
                var r,
                    i;
                for (i = 0; n.length > i; i++)
                    null !== n[i] && (r = e.data(t + n[i]), void 0 === r && (r = ""), e.css(n[i], r))
            },
            setMode: function(e, t) {
                return "toggle" === t && (t = e.is(":hidden") ? "show" : "hide"), t
            },
            getBaseline: function(e, t) {
                var n,
                    r;
                switch (e[0]) {
                case "top":
                    n = 0;
                    break;
                case "middle":
                    n = .5;
                    break;
                case "bottom":
                    n = 1;
                    break;
                default:
                    n = e[0] / t.height
                }
                switch (e[1]) {
                case "left":
                    r = 0;
                    break;
                case "center":
                    r = .5;
                    break;
                case "right":
                    r = 1;
                    break;
                default:
                    r = e[1] / t.width
                }
                return {
                    x: r,
                    y: n
                }
            },
            createWrapper: function(t) {
                if (t.parent().is(".ui-effects-wrapper"))
                    return t.parent();
                var n = {
                        width: t.outerWidth(!0),
                        height: t.outerHeight(!0),
                        "float": t.css("float")
                    },
                    r = e("<div></div>").addClass("ui-effects-wrapper").css({
                        fontSize: "100%",
                        background: "transparent",
                        border: "none",
                        margin: 0,
                        padding: 0
                    }),
                    i = {
                        width: t.width(),
                        height: t.height()
                    },
                    s = document.activeElement;
                try {
                    s.id
                } catch (o) {
                    s = document.body
                }
                return t.wrap(r), (t[0] === s || e.contains(t[0], s)) && e(s).focus(), r = t.parent(), "static" === t.css("position") ? (r.css({
                    position: "relative"
                }), t.css({
                    position: "relative"
                })) : (e.extend(n, {
                    position: t.css("position"),
                    zIndex: t.css("z-index")
                }), e.each(["top", "left", "bottom", "right"], function(e, r) {
                    n[r] = t.css(r), isNaN(parseInt(n[r], 10)) && (n[r] = "auto")
                }), t.css({
                    position: "relative",
                    top: 0,
                    left: 0,
                    right: "auto",
                    bottom: "auto"
                })), t.css(i), r.css(n).show()
            },
            removeWrapper: function(t) {
                var n = document.activeElement;
                return t.parent().is(".ui-effects-wrapper") && (t.parent().replaceWith(t), (t[0] === n || e.contains(t[0], n)) && e(n).focus()), t
            },
            setTransition: function(t, n, r, i) {
                return i = i || {}, e.each(n, function(e, n) {
                    var o = t.cssUnit(n);
                    o[0] > 0 && (i[n] = o[0] * r + o[1])
                }), i
            }
        }), e.fn.extend({
            effect: function() {
                function t(t) {
                    function n() {
                        e.isFunction(s) && s.call(i[0]), e.isFunction(t) && t()
                    }
                    var i = e(this),
                        s = r.complete,
                        o = r.mode;
                    (i.is(":hidden") ? "hide" === o : "show" === o) ? (i[o](), n()) : u.call(i[0], r, n)
                }
                var r = n.apply(this, arguments),
                    s = r.mode,
                    o = r.queue,
                    u = e.effects.effect[r.effect];
                return e.fx.off || !u ? s ? this[s](r.duration, r.complete) : this.each(function() {
                    r.complete && r.complete.call(this)
                }) : o === !1 ? this.each(t) : this.queue(o || "fx", t)
            },
            show: function(e) {
                return function(t) {
                    if (r(t))
                        return e.apply(this, arguments);
                    var o = n.apply(this, arguments);
                    return o.mode = "show", this.effect.call(this, o)
                }
            }(e.fn.show),
            hide: function(e) {
                return function(t) {
                    if (r(t))
                        return e.apply(this, arguments);
                    var o = n.apply(this, arguments);
                    return o.mode = "hide", this.effect.call(this, o)
                }
            }(e.fn.hide),
            toggle: function(e) {
                return function(t) {
                    if (r(t) || "boolean" == typeof t)
                        return e.apply(this, arguments);
                    var o = n.apply(this, arguments);
                    return o.mode = "toggle", this.effect.call(this, o)
                }
            }(e.fn.toggle),
            cssUnit: function(t) {
                var n = this.css(t),
                    r = [];
                return e.each(["em", "px", "%", "pt"], function(e, t) {
                    n.indexOf(t) > 0 && (r = [parseFloat(n), t])
                }), r
            }
        })
    }(), function() {
        var t = {};
        e.each(["Quad", "Cubic", "Quart", "Quint", "Expo"], function(e, n) {
            t[n] = function(t) {
                return Math.pow(t, e + 2)
            }
        }), e.extend(t, {
            Sine: function(e) {
                return 1 - Math.cos(e * Math.PI / 2)
            },
            Circ: function(e) {
                return 1 - Math.sqrt(1 - e * e)
            },
            Elastic: function(e) {
                return 0 === e || 1 === e ? e : -Math.pow(2, 8 * (e - 1)) * Math.sin((80 * (e - 1) - 7.5) * Math.PI / 15)
            },
            Back: function(e) {
                return e * e * (3 * e - 2)
            },
            Bounce: function(e) {
                for (var t, n = 4; ((t = Math.pow(2, --n)) - 1) / 11 > e;)
                    ;
                return 1 / Math.pow(4, 3 - n) - 7.5625 * Math.pow((3 * t - 2) / 22 - e, 2)
            }
        }), e.each(t, function(t, n) {
            e.easing["easeIn" + t] = n, e.easing["easeOut" + t] = function(e) {
                return 1 - n(1 - e)
            }, e.easing["easeInOut" + t] = function(e) {
                return .5 > e ? n(2 * e) / 2 : 1 - n(-2 * e + 2) / 2
            }
        })
    }(), e.effects
}), !function(e) {
    "function" == typeof define && define.amd ? define("jquery_cookie", ["jquery"], e) : "object" == typeof exports ? e(require("jquery")) : e(jQuery)
}(function(e) {
    function t(e) {
        return u.raw ? e : encodeURIComponent(e)
    }
    function n(e) {
        return u.raw ? e : decodeURIComponent(e)
    }
    function r(e) {
        return t(u.json ? JSON.stringify(e) : String(e))
    }
    function i(e) {
        0 === e.indexOf('"') && (e = e.slice(1, -1).replace(/\\"/g, '"').replace(/\\\\/g, "\\"));
        try {
            return e = decodeURIComponent(e.replace(o, " ")), u.json ? JSON.parse(e) : e
        } catch (t) {}
    }
    function s(t, n) {
        var r = u.raw ? t : i(t);
        return e.isFunction(n) ? n(r) : r
    }
    var o = /\+/g,
        u = e.cookie = function(i, o, l) {
            if (void 0 !== o && !e.isFunction(o)) {
                if (l = e.extend({}, u.defaults, l), "number" == typeof l.expires) {
                    var p = l.expires,
                        v = l.expires = new Date;
                    v.setTime(+v + 864e5 * p)
                }
                return document.cookie = [t(i), "=", r(o), l.expires ? "; expires=" + l.expires.toUTCString() : "", l.path ? "; path=" + l.path : "", l.domain ? "; domain=" + l.domain : "", l.secure ? "; secure" : ""].join("")
            }
            for (var m = i ? void 0 : {}, g = document.cookie ? document.cookie.split("; ") : [], y = 0, w = g.length; w > y; y++) {
                var E = g[y].split("="),
                    S = n(E.shift()),
                    x = E.join("=");
                if (i && i === S) {
                    m = s(x, o);
                    break
                }
                i || void 0 === (x = s(x)) || (m[S] = x)
            }
            return m
        };
    u.defaults = {}, e.removeCookie = function(t, n) {
        return void 0 === e.cookie(t) ? !1 : (e.cookie(t, "", e.extend({}, n, {
            expires: -1
        })), !e.cookie(t))
    }
}), define("frontend/Analytics", ["jquery", "jquery_cookie"], function(e, t) {
    var n = function(t) {
            var n = this,
                r,
                i,
                s,
                o;
            r = {
                name: "Analytics",
                pageProperties: null,
                started: !1,
                suspended: !1,
                processing: !1,
                nextItemId: null,
                pvCount: null,
                queue: [],
                definedEvents: {},
                requiredProperties: ["page name", "page url", "source page type", "source domain", "visit type"],
                skipEagerAmbientPropertyCapture: !1,
                newVisit: !1,
                newUser: null,
                gaCustomDim: {
                    category: null,
                    authors: null
                },
                IS_QA: window.location.hostname.indexOf("www.good-qa") === 0 || window.location.hostname.indexOf("local") === 0 || window.location.hostname.indexOf("sports.good-qa") === 0 || window.location.hostname.indexOf(".good-qa.com") !== -1,
                tdgVisitor: !1,
                vCount: 0
            }, i = {
                LOGGING_COOKIE_NAME: "good_analytics_logging_enabled",
                MIXPANEL_UUID_REGEXP: /^[a-f0-9]+-[a-f0-9]+-[a-f0-9]+-[a-f0-9]+-[a-f0-9]+$/,
                GA_TRACKER: r.IS_QA ? "UA-1694058-30" : "UA-1694058-27"
            }, s = {
                init: function() {
                    s.initVars(), s.setSourceCookie(), s.initGA(), s.initMixpanel(), s.initQuantcast(), s.initComscore(), o.start(r.config), s.initMixpanelEvents(), s.initMixpanelHandlers()
                },
                initVars: function() {
                    r.nextItemId = parseInt(s.getSessionStorage("nextItemId") || "0", 10), r.pvCount = parseInt(s.getSessionStorage("pvCount") || "0", 10), r.queue = JSON.parse(s.getSessionStorage("queue") || "[]"), r.vCount = parseInt(s.getLocalStorage("vCount") || "0", 10), r.pvCount == 0 ? (r.newUser = document.cookie.indexOf("mp_gd") == -1, s.setSessionStorage("newUser", r.newUser)) : r.newUser = s.getSessionStorage("newUser") == "true", r.config = e.extend(window.MixPanel.extras, {
                        "page name": document.title,
                        "page url": window.location.pathname + window.location.hash,
                        "visit type": r.newUser ? "new" : "returning"
                    }), e.cookie("u") && (r.config.u = e.cookie("u")), window.MixPanel.extras.category && (r.gaCustomDim.category = window.MixPanel.extras.category), window.MixPanel.extras.authors && (r.gaCustomDim.authors = window.MixPanel.extras.authors.join(","))
                },
                initGA: function() {
                    s.remove_root_cookies(/^(__utm.)=/), function(e, t, n, r, i, s, o) {
                        e.GoogleAnalyticsObject = i, e[i] = e[i] || function() {
                            (e[i].q = e[i].q || []).push(arguments)
                        }, e[i].l = 1 * new Date, s = t.createElement(n), o = t.getElementsByTagName(n)[0], s.async = 1, s.src = r, o.parentNode.insertBefore(s, o)
                    }(window, document, "script", "//www.google-analytics.com/analytics.js", "ga"), ga("create", i.GA_TRACKER, "auto"), ga("set", "page", window.location.pathname + window.location.hash), r.gaCustomDim.category && ga("set", "dimension1", r.gaCustomDim.category), r.gaCustomDim.authors && ga("set", "dimension2", r.gaCustomDim.authors), ga("send", "pageview", {
                        hitCallback: function() {
                            s.logMessage("GA Pageview Logged")
                        }
                    })
                },
                initChartbeat: function() {
                    var e = r.IS_QA ? "www.good-qa.com" : "good.is",
                        t = {
                            uid: 2224,
                            domain: e,
                            useCanonical: !0,
                            sections: window.MixPanel.extras["source page type"]
                        };
                    window.MixPanel.extras.authors && (t.authors = window.MixPanel.extras.authors.join(",")), window._sf_async_config = t, function() {
                        window._sf_endpt = (new Date).getTime();
                        var e = document.createElement("script");
                        e.setAttribute("language", "javascript"), e.setAttribute("type", "text/javascript"), e.setAttribute("src", "//static.chartbeat.com/js/chartbeat_video.js"), document.body.appendChild(e), window._cbv = window._cbv || [], window._cbv.push(["autoDetectYouTubeIframes"])
                    }()
                },
                initMixpanel: function() {
                    s.remove_root_cookies(/^(mp_good_mixpanel_[^=]+|mp_[^m]+_mixpanel)=/), function(e, t) {
                        if (!t.__SV) {
                            var n,
                                r,
                                i,
                                s;
                            window.mixpanel = t, n = e.createElement("script"), n.type = "text/javascript", n.async = !0, n.src = ("https:" === e.location.protocol ? "https:" : "http:") + "//cdn.mxpnl.com/libs/mixpanel-2.2.min.js", r = e.getElementsByTagName("script")[0], r.parentNode.insertBefore(n, r), t._i = [], t.init = function(e, n, r) {
                                function o(e, t) {
                                    var n = t.split(".");
                                    2 == n.length && (e = e[n[0]], t = n[1]), e[t] = function() {
                                        e.push([t].concat(Array.prototype.slice.call(arguments, 0)))
                                    }
                                }
                                var u = t;
                                "undefined" != typeof r ? u = t[r] = [] : r = "mixpanel", u.people = u.people || [], u.toString = function(e) {
                                    var t = "mixpanel";
                                    return "mixpanel" !== r && (t += "." + r), e || (t += " (stub)"), t
                                }, u.people.toString = function() {
                                    return u.toString(1) + ".people (stub)"
                                }, i = "disable track track_pageview track_links track_forms register register_once alias unregister identify name_tag set_config people.set people.set_once people.increment people.append people.track_charge people.clear_charges people.delete_user".split(" ");
                                for (s = 0; s < i.length; s++)
                                    o(u, i[s]);
                                t._i.push([e, n, r])
                            }, t.__SV = 1.2
                        }
                    }(document, window.mixpanel || []);
                    var e = "15a73809c334ba4a759672cc9c690311";
                    window.location.hostname.indexOf("good-qa.com") != -1 && (e = "2f91447b96174751125ae6d2f12a0794"), window.location.hostname.indexOf("goodalpaca") != -1 && (e = "82e31772c4ddcdd52584ab6d16f0b406"), mixpanel.init(e, {
                        track_pageview: !1,
                        cross_subdomain_cookie: !0,
                        cookie_name: "gd_" + e
                    })
                },
                initQuantcast: function() {
                    (function() {
                        window._qevents = window._qevents || [], window._qevents.push({
                            qacct: "p-4c0hwNZOgOTUw"
                        });
                        var e = document.createElement("script");
                        e.src = (document.location.protocol == "https:" ? "https://secure" : "http://edge") + ".quantserve.com/quant.js", e.async = !0, e.type = "text/javascript";
                        var t = document.getElementsByTagName("script")[0];
                        t.parentNode.insertBefore(e, t)
                    })()
                },
                initComscore: function() {
                    s.load_script((document.location.protocol == "https:" ? "https://sb" : "http://b") + ".scorecardresearch.com/beacon.js", function() {
                        COMSCORE.beacon({
                            c1: 2,
                            c2: 7280709
                        })
                    })
                },
                initMixpanelEvents: function() {
                    o.defineEvent("Pageview"), o.defineEvent("Visit"), o.defineEvent("Header Item Click", {
                        required: ["target"]
                    }), o.defineEvent("Sidenav Item Click", {
                        required: ["target"]
                    }), o.defineEvent("Sidebar Ranking Item Clicked"), o.defineEvent("Share Content", {
                        required: ["target", "location"]
                    }), o.defineEvent("Video Action", {
                        required: ["event", "location"]
                    }), o.defineEvent("Scrolled 50% Post Content"), o.defineEvent("Impression", {
                        required: ["placement", "content"]
                    }), o.defineEvent("Author Module Click", {
                        required: ["target"]
                    })
                },
                initMixpanelHandlers: function() {
                    r.pvCount++, location.search.indexOf("utm_campaign=dailygood") !== -1 && e.cookie("tdg_visitor", !0, {
                        expires: 90,
                        path: "/"
                    });
                    var t = e(".mailchimp-widget");
                    e.cookie("tdg_visitor") === "true" ? (window.MixPanel.extras["Daily GOOD Subscriber"] = !0, t.remove(), e(".socials-widget").show(), r.tdgVisitor = !0) : t.length && (e(".socials-widget").remove(), t.show()), r.newVisit && (r.vCount = parseInt(s.getLocalStorage("vCount")) || r.vCount, r.vCount += 1, s.setLocalStorage("vCount", r.vCount), o.track("Visit"));
                    var n = e("[data-dogear-type]").filter(":visible").first();
                    o.track("Pageview", {
                        dogear: n.length > 0 ? n.data("dogear-type") : null
                    })
                },
                setSourceCookie: function() {
                    var t = e.cookie("gd_v");
                    if (!t || t.indexOf("|") == -1)
                        r.newVisit = !0, r.config["source domain"] = s.parseUri(document.referrer).host || "direct", r.config.sid = s.extractSourceID() || "", t = r.config["source domain"] + "|" + r.config.sid;
                    else {
                        var n = t.split("|");
                        r.config["source domain"] = n[0], r.config.sid = s.extractSourceID() || n[1]
                    }
                    r.config.sid.length || delete r.config.sid;
                    var i = new Date,
                        o = i.getTime() + 18e5;
                    i.setTime(o), e.cookie("gd_v", t, {
                        expires: i,
                        path: "/",
                        domain: window.location.hostname.substring(window.location.hostname.indexOf("."), window.location.hostname.length)
                    })
                },
                prettyFormatProperties: function(e) {
                    var t = "",
                        n = 0;
                    for (var r in e) {
                        if (!e.hasOwnProperty(r))
                            continue;
                        r.length > n && (n = r.length)
                    }
                    for (var r in e) {
                        if (!e.hasOwnProperty(r))
                            continue;
                        t += ((new Array(n)).join(" ") + r).slice(-n) + " : " + e[r] + "\n"
                    }
                    return t
                },
                logItem: function(e, t) {
                    if (s.isLoggingEnabled()) {
                        var n = "analytics event: " + e + '\n~~~ "' + t.eventName + '" (ID ' + t.id + ")\n";
                        n += s.prettyFormatProperties(t.properties), console.log(n)
                    }
                },
                logMessage: function(e) {
                    s.isLoggingEnabled() && console.log("analytics:", e)
                },
                isLoggingEnabled: function() {
                    return e.cookie(i.LOGGING_COOKIE_NAME) == "1"
                },
                getSessionStorage: function(e) {
                    return sessionStorage["good_analytics_" + e]
                },
                setSessionStorage: function(e, t) {
                    sessionStorage.length > 10 && sessionStorage.clear();
                    if (t)
                        try {
                            sessionStorage["good_analytics_" + e] = JSON.stringify(t)
                        } catch (n) {
                            console.error("Error saving analytics message queue to sessionStorage", n)
                        }
                    else
                        delete sessionStorage["good_analytics_" + e]
                },
                getLocalStorage: function(e) {
                    return localStorage !== undefined ? localStorage["good_analytics_" + e] : undefined
                },
                setLocalStorage: function(e, t) {
                    if (t)
                        try {
                            localStorage["good_analytics_" + e] = JSON.stringify(t)
                        } catch (n) {
                            console.error("Error saving analytics to localStorage", n)
                        }
                    else
                        delete localStorage["good_analytics_" + e]
                },
                saveQueue: function() {
                    s.setSessionStorage("queue", r.queue.length == 0 ? null : r.queue), s.setSessionStorage("nextItemId", r.nextItemId), s.setSessionStorage("pvCount", r.pvCount)
                },
                remove_root_cookies: function(e) {
                    var t = document.cookie.split(";");
                    for (var n = 0; n < t.length; n++) {
                        var r = t[n].trim(),
                            i = r.match(e);
                        i && (document.cookie = i[1] + "=;path=/;domain=.good.is;expires=Thu, 01 Jan 1970 00:00:01 GMT;")
                    }
                },
                extractSourceID: function() {
                    var t = s.parseUri(document.URL).queryKey.sid || "";
                    if (t && !!window.history && !!history.replaceState) {
                        var n = s.parseUri(document.URL),
                            r = n.queryKey,
                            i = n.anchor;
                        delete r.sid;
                        var o = e.param(r);
                        o = (o ? "?" + o : "") + (i ? "#" + i : ""), history.replaceState({
                            sourceID: t
                        }, document.title, window.location.pathname + o)
                    }
                    return t
                },
                parseUri: function(e) {
                    var t = {
                            strictMode: !1,
                            key: ["source", "protocol", "authority", "userInfo", "user", "password", "host", "port", "relative", "path", "directory", "file", "query", "anchor"],
                            q: {
                                name: "queryKey",
                                parser: /(?:^|&)([^&=]*)=?([^&]*)/g
                            },
                            parser: {
                                strict: /^(?:([^:\/?#]+):)?(?:\/\/((?:(([^:@]*)(?::([^:@]*))?)?@)?([^:\/?#]*)(?::(\d*))?))?((((?:[^?#\/]*\/)*)([^?#]*))(?:\?([^#]*))?(?:#(.*))?)/,
                                loose: /^(?:(?![^:@]+:[^:@\/]*@)([^:\/?#.]+):)?(?:\/\/)?((?:(([^:@]*)(?::([^:@]*))?)?@)?([^:\/?#]*)(?::(\d*))?)(((\/(?:[^?#](?![^?#\/]*\.[^?#\/.]+(?:[?#]|$)))*\/?)?([^?#\/]*))(?:\?([^#]*))?(?:#(.*))?)/
                            }
                        },
                        n = t.parser[t.strictMode ? "strict" : "loose"].exec(e),
                        r = {},
                        i = 14;
                    while (i--)
                        r[t.key[i]] = n[i] || "";
                    return r[t.q.name] = {}, r[t.key[12]].replace(t.q.parser, function(e, n, i) {
                        n && (r[t.q.name][n] = i)
                    }), r
                },
                load_script: function(t, n) {
                    if (typeof n == "function")
                        e.getScript(t, n);
                    else {
                        var r = document.getElementsByTagName("script")[0],
                            i = document.createElement("script");
                        i.type = "text/javascript", i.async = !0, i.src = t, r.parentNode.insertBefore(i, r)
                    }
                },
                removeFromQueue: function(e) {
                    var t = !1;
                    for (var n = 0; n < r.queue.length; n++) {
                        var i = r.queue[n];
                        if (i.id == e.id) {
                            r.queue.splice(n, 1), t = !0;
                            break
                        }
                    }
                    if (!t)
                        throw new Error("BUG: item should always be in queue");
                    s.saveQueue()
                },
                processQueue: function() {
                    if (r.processing || r.suspended)
                        return;
                    r.processing = !0;
                    var e = r.queue[0];
                    if (!e) {
                        r.processing = !1;
                        return
                    }
                    s.captureAmbientProperties(e);
                    var t = o.checkEventForErrors(e.eventName, e.properties);
                    if (t.length > 0) {
                        var n = 'analytics event: Event failed validation\n~~~ "' + e.eventName + '" (ID ' + e.id + ")\n";
                        n += "Failing properties: " + t.map(function(e) {
                            return '"' + e + '"'
                        }).join(", ") + "\n", n += s.prettyFormatProperties(e.properties), console.error(n), e.properties.__good_event_invalid = t.map(function(e) {
                            return '"' + e + '"'
                        }).join(", ")
                    }
                    s.removeFromQueue(e), mixpanel.track(e.eventName, e.properties, function(t) {
                        t == 1 ? (s.logItem("Successfully sent to Mixpanel", e), r.processing = !1, s.processQueue()) : setTimeout(function() {
                            r.processing = !1, s.processQueue()
                        }, 1e3)
                    })
                },
                captureAmbientProperties: function(t) {
                    if (!r.started || t.ambientPropertiesCaptured)
                        return;
                    var n = {};
                    if (mixpanel.cookie)
                        for (var i in mixpanel.cookie.props) {
                            if (!mixpanel.cookie.props.hasOwnProperty(i))
                                continue;
                            i.match(/^__mp/) || (n[i] = mixpanel.cookie.props[i])
                        }
                    t.properties = e.extend({}, n, r.pageProperties, t.properties), t.ambientPropertiesCaptured = !0
                }
            }, o = {
                delayUntilNextPage: function() {
                    s.logMessage("Suspending analytics events until next page (will skip eager ambient property capture)"), suspended = !0, r.skipEagerAmbientPropertyCapture = !0
                },
                aliasUser: function(e) {
                    i.MIXPANEL_UUID_REGEXP.test(mixpanel.get_distinct_id()) ? (mixpanel.alias(e), s.logMessage("mixpanel.alias('" + e + "')")) : (mixpanel.identify(e), s.logMessage("mixpanel.identify('" + e + "')"))
                },
                identifyUser: function(e) {
                    mixpanel.identify(e), s.logMessage("mixpanel.identify('" + e + "')")
                },
                track: function(e, t) {
                    t = t || {};
                    if (!e)
                        throw new Error("BUG: empty eventName passed to analytics.track");
                    var n = {
                        id: String(r.nextItemId++),
                        eventName: e,
                        properties: t
                    };
                    t["event num"] = n.id, t["pageview count"] = r.pvCount, t["visit count"] = r.vCount, t["tdg subscriber"] = r.tdgVisitor, r.skipEagerAmbientPropertyCapture || s.captureAmbientProperties(n), r.queue.push(n), r.queue.length > 100 && r.queue.shift(), s.saveQueue(), r.started && setTimeout(s.processQueue, 0)
                },
                trackPageview: function(e) {
                    typeof COMSCORE != "undefined" && (s.logMessage("comScore Pageview Logged"), COMSCORE.beacon({
                        c1: 2,
                        c2: 7280709
                    })), ga("send", "pageview", {
                        path: e["page url"],
                        title: e["page name"],
                        hitCallback: function(e) {
                            s.logMessage("GA Pageview Logged")
                        }
                    }), r.pvCount++, o.track("Pageview", e)
                },
                enableLogging: function() {
                    e.cookie(i.LOGGING_COOKIE_NAME, "1", {
                        path: "/"
                    })
                },
                disableLogging: function() {
                    e.cookie(i.LOGGING_COOKIE_NAME, null, {
                        path: "/"
                    })
                },
                start: function(e) {
                    if (!e)
                        throw new Error("BUG: properties are missing");
                    if (r.pageProperties)
                        throw new Error("BUG: analytics.start has already been called");
                    r.pageProperties = e, mixpanel.push(function() {
                        r.started = !0, setTimeout(s.processQueue, 0)
                    })
                },
                checkEventForErrors: function(e, n) {
                    var i = [];
                    try {
                        if (t = r.definedEvents[e]) {
                            for (var s = 0; s < t.required.length; s++) {
                                var o = t.required[s];
                                !n[o] && n[o] != 0 && i.push(o)
                            }
                            var u;
                            (u = t.prepare) && u(n, function(e) {
                                i.push(e)
                            })
                        } else
                            i.push('Analytics event "' + e + '" has not been defined')
                    } catch (a) {
                        i.push(a)
                    }
                    return i
                },
                defineEvent: function(e, t) {
                    t = t || {}, t.required = (t.required || []).concat(r.requiredProperties);
                    var n;
                    if (n = t.prepare)
                        t.prepare = function() {
                            var e = 1 <= arguments.length ? slice.call(arguments, 0) : [];
                            n.apply(null, e)
                        };
                    if (r.definedEvents[e])
                        throw new Error('BUG: analytics event "' + e + '" has already been defined');
                    r.definedEvents[e] = t
                }
            }, this.track = o.track, this.trackPageview = o.trackPageview, s.init()
        },
        r = null;
    return function() {
        return r || (r = new n), r
    }
}), define("frontend/SlidenavAccordion", ["jquery", "frontend/globals", "jquery_easing", "frontend/Analytics"], function(e, t, n, r) {
    var i = function(n) {
        var i = this,
            s,
            o,
            u,
            a,
            f,
            l,
            c,
            h;
        s = e.extend({
            $e: null,
            selector: "",
            slide_duration: 300,
            slide_easing: "easeOutQuart"
        }, n), o = t(), u = r(), a = {
            CURRENT: "current",
            SECTION: "accord-section",
            SECTION_HEAD: "js-accord-hd",
            SECTION_BODY: "js-accord-bd"
        }, f = {
            name: "SlidenavAccordion",
            $e: s.$e || e(s.selector)
        }, l = {
            hds: f.$e.find(".js-accord-hd")
        }, c = {
            init: function() {
                l.hds.click(h.hd_click)
            },
            get_section_by_name: function(e) {
                return f.$e.find("." + a.SECTION + '[data-section="' + e + '"]')
            },
            close: function(e) {
                typeof e == "string" && (e = c.get_section_by_name(e)), e.find("." + a.SECTION_HEAD).removeClass(a.CURRENT), e.find("." + a.SECTION_BODY).slideUp({
                    duration: s.slide_duration,
                    easing: s.slide_easing
                })
            },
            open: function(e) {
                var t;
                typeof e == "string" && (e = c.get_section_by_name(e)), t = e.siblings(), t.find("." + a.SECTION_HEAD).removeClass(a.CURRENT), e.find("." + a.SECTION_HEAD).addClass(a.CURRENT), t.find("." + a.SECTION_BODY).slideUp({
                    duration: s.slide_duration,
                    easing: s.slide_easing
                }), e.find("." + a.SECTION_BODY).slideDown({
                    duration: s.slide_duration,
                    easing: s.slide_easing
                })
            },
            toggle: function(e) {
                c[e.find("." + a.SECTION_HEAD).hasClass(a.CURRENT) ? "close" : "open"](e)
            }
        }, h = {
            hd_click: function() {
                c.toggle(e(this).parent("." + a.SECTION)), u.track("Sidenav Item Click", {
                    target: e(this).data("target")
                })
            }
        }, i.close = c.close, i.open = c.open, c.init()
    };
    return i
}), define("frontend/AtticAd", ["jquery"], function(e) {
    var t = function(t) {
        var n = this,
            r,
            i,
            s,
            o;
        r = e.extend({
            $e: null,
            selector: ""
        }, t), i = {
            $e: r.$e || e(r.selector)
        }, s = {
            container: e(".container"),
            ad: i.$e.find(".ad")
        }, o = {
            init: function() {
                e(window).width() < 768 ? i.$e.addClass("small-attic") : e(window).width() < 1016 ? i.$e.addClass("full-attic") : i.$e.addClass("no-fix"), setTimeout(function() {
                    var e = i.$e.find(".ad iframe");
                    e.length > 0 ? setTimeout(function() {
                        o.hideAd()
                    }, 9e3) : o.hideAd()
                }, 1e3)
            },
            hideAd: function() {
                var t = -Math.min(i.$e.outerHeight(), e("body").scrollTop());
                s.ad.animate({
                    top: t
                }, 500, function() {
                    s.ad.css({
                        top: "",
                        position: "relative"
                    }), i.$e.addClass("no-fix")
                })
            }
        }, o.init()
    };
    return t
}), define("frontend/Header", ["jquery", "frontend/globals", "jquery_easing", "frontend/Analytics", "frontend/SlidenavAccordion", "frontend/AtticAd"], function(e, t, n, r, i, s) {
    var o = function(n) {
        var o = this,
            u,
            a,
            f,
            l,
            c,
            h,
            p;
        u = e.extend({
            $e: null,
            selector: "",
            use_following_main_header: !1,
            fixed_header_threshold: 550,
            fb_page_id: "13152108058"
        }, n), a = t(), f = r(), l = {
            name: "Header",
            $e: u.$e || e(u.selector),
            main_header_follow_dist: 0,
            main_header_state: "normal",
            fixie_header_state: "normal",
            secondary_feats_showing: !1,
            main_header_follow_pos: 0,
            metanav_height: 0,
            win_height: a.elements.window.height(),
            slidenav_accordion: null,
            attic_ad: null,
            nag_window_is_on_page: !1,
            nag_window_appears_at: 0,
            nag_window_visible: !1,
            has_homepage_header_ad: !1,
            scroll_top: 0,
            iframe_hover: {
                fb: !1,
                twitter: !1
            }
        }, c = {
            main_header: l.$e.find(".js-header"),
            fixie_header: l.$e.find(".js-fixie-header"),
            homepage_header_ad: l.$e.find("#ad_homepage_header"),
            logo: l.$e.find(".js-logo"),
            pulltab: l.$e.find(".js-pulltab"),
            feats: a.elements.header.find(".js-feat"),
            sponsor_link: a.elements.header.find(".js-feat .sponsor-widget a"),
            nav_links: a.elements.header.find(".navitems a:not(.js-search-trigger)"),
            community_link: a.elements.metanav.find("a:last"),
            socials: a.elements.header.find(".js-social"),
            fb_like_count: a.elements.header.find(".js-fb-count"),
            search_trigger: l.$e.find(".js-search-trigger"),
            searchbox: l.$e.find(".js-searchbox"),
            slidenav_trigger: l.$e.find(".js-slidenav-trigger"),
            slidenav: l.$e.find(".js-slidenav"),
            nag_window: l.$e.find(".js-nag-window"),
            nag_copy_url: l.$e.find(".js-nag-window a.url input"),
            article: {
                hero: e("article .hero"),
                titleblock: e("article .titleblock")
            }
        }, h = {
            init: function() {
                h.setup_follow_distance(), u.use_following_main_header && c.feats.each(function() {
                    e(this).css({
                        "will-change": "transform",
                        "-webkit-backface-visibility": "hidden",
                        "backface-visibility": "hidden"
                    })
                }), setTimeout(function() {
                    l.has_homepage_header_ad = c.homepage_header_ad.is(":visible")
                }, 2e3), c.feats.each(function() {
                    var t = e(this);
                    t.data("track", t.find(".js-track")), t.data("height", t.height())
                }), c.fixie_header.show(), h.resize_slidenav(), l.slidenav_accordion = new i({
                    $e: c.slidenav.find(".accordion")
                }), l.attic_ad = new s({
                    $e: l.$e.find(".attic-cont")
                });
                if (c.nag_window.length > 0) {
                    l.nag_window_is_on_page = !0;
                    var t = e("article .copy").last();
                    t.length > 0 ? l.nag_window_appears_at = t.offset().top + t.height() - l.win_height * 1.5 : l.nag_window_appears_at = a.elements.document.height() - l.win_height * 5, l.nag_window_appears_at < l.win_height * 2 && (l.nag_window_appears_at = l.win_height * 2)
                }
                c.pulltab.click(p.pulltab_click), c.slidenav_trigger.click(p.slidenav_trigger_click), c.search_trigger.click(p.search_trigger_click), c.searchbox.on("keypress", p.search_keypress), c.socials.on("mouseenter", p.social_mouseenter), c.socials.click(p.social_click), c.nav_links.click(p.nav_link_click), c.sponsor_link.click(p.sponsor_img_click), c.community_link.click(p.community_link_click), c.logo.click(p.logo_click), c.nag_copy_url.click(p.nag_copy_url_click), a.elements.document.on("scroll_simple", p.scroll), a.elements.document.on("resize_debounced", p.resize), e(window).blur(p.iframe_hover_check)
            },
            setup_follow_distance: function() {
                var e = c.article.hero,
                    t = c.article.titleblock,
                    n = c.main_header.outerHeight();
                if (e.length > 0 && t.length > 0 && c.main_header.length > 0) {
                    var r = parseInt(t.css("margin-top").replace("px", ""), 10);
                    r < 90 && (r = 90);
                    var i = parseInt(c.main_header.css("border-bottom-width").replace("px", ""), 10);
                    l.main_header_follow_dist = t.offset().top - r + i / 2 - n, u.fixed_header_threshold = l.main_header_follow_dist + n
                } else
                    l.main_header_follow_dist = n * .19
            },
            fix_header: function() {
                c.fixie_header.addClass("state-fixed"), l.fixie_header_state = "fixed"
            },
            unfix_header: function() {
                c.fixie_header.removeClass("state-fixed"), l.fixie_header_state = "normal"
            },
            main_header_follow: function() {
                var t,
                    n,
                    r;
                r = 9, t = l.scroll_top < l.main_header_follow_dist ? l.scroll_top - l.metanav_height : l.main_header_follow_dist - l.metanav_height, t = t < 0 ? 0 : t, l.main_header_state != "normal" && l.scroll_top > t ? (l.main_header_state = "normal", c.main_header.css({
                    position: "absolute",
                    top: t
                })) : l.main_header_state != "fixed" && l.scroll_top <= t && (l.main_header_state = "fixed", c.main_header.css({
                    position: "fixed",
                    top: l.metanav_height
                })), l.scroll_top > r && !l.secondary_feats_showing ? (c.feats.each(function(t) {
                    var n = e(this),
                        r = "translate3d(0," + -1 * n.data("height") + "px, 0)";
                    n.data("track").css({
                        "-webkit-transform": r,
                        "-moz-transform": r,
                        "-ms-transform": r,
                        transform: r
                    })
                }), l.secondary_feats_showing = !0) : l.scroll_top <= r && l.secondary_feats_showing && (c.feats.each(function(t) {
                    var n = e(this),
                        r = "translate3d(0, 0, 0)";
                    n.data("track").css({
                        "-webkit-transform": r,
                        "-moz-transform": r,
                        "-ms-transform": r,
                        transform: r
                    })
                }), l.secondary_feats_showing = !1), l.main_header_follow_pos = t
            },
            toggle_slidenav: function() {
                a.elements.body.toggleClass("slidenav-open")
            },
            open_slidenav: function() {
                a.elements.body.addClass("slidenav-open")
            },
            resize_slidenav: function() {
                var t = l.win_height;
                c.slidenav.find(".js-accord-hd").each(function() {
                    t -= e(this).outerHeight()
                }), t < 250 && (t = 250), c.slidenav.find(".js-accord-bd").css({
                    "max-height": t - 40 - 2
                })
            },
            load_social: function(t) {
                if (!t.data("loaded")) {
                    t.data("loaded", !0);
                    var n = t.find(".js-hovered").html('<div class="vcenter-outer"><div class="vcenter-inner">' + t.find(".js-hovered").data("html") + "</div></div>"),
                        r;
                    n.data("html").indexOf("facebook") > -1 ? r = "fb" : r = "twitter", window.setTimeout(function() {
                        e("iframe", n).hover(function(e) {
                            l.iframe_hover[r] = !0
                        }, function(e) {
                            l.iframe_hover[r] = !1
                        })
                    }, r == "twitter" ? 100 : 0)
                }
            },
            track_header_click: function(e) {
                f.track("Header Item Click", {
                    target: e
                })
            }
        }, p = {
            scroll: function(e) {
                l.scroll_top = e.scroll_top, c.fixie_header.length > 0 && (l.scroll_top >= u.fixed_header_threshold && l.fixie_header_state != "fixed" ? h.fix_header() : l.scroll_top < u.fixed_header_threshold && l.fixie_header_state != "normal" && h.unfix_header()), u.use_following_main_header && !l.has_homepage_header_ad && !a.features.can_touch && (l.scroll_top < l.main_header_follow_dist || l.main_header_follow_pos + l.metanav_height < l.main_header_follow_dist) && h.main_header_follow(), l.nag_window_is_on_page && (!l.nag_window_visible && l.scroll_top > l.nag_window_appears_at ? (c.nag_window.addClass("state-fixed"), l.nag_window_visible = !0) : l.nag_window_visible && l.scroll_top < l.nag_window_appears_at && (c.nag_window.removeClass("state-fixed"), l.nag_window_visible = !1))
            },
            resize: function(e) {
                l.win_height = e.win_height, h.resize_slidenav(), h.setup_follow_distance(), u.use_following_main_header && !l.has_homepage_header_ad && !a.features.can_touch && h.main_header_follow()
            },
            pulltab_click: function(e) {
                h.toggle_slidenav(), h.track_header_click("Pulltab")
            },
            slidenav_trigger_click: function(t) {
                var n;
                t.preventDefault(), h.toggle_slidenav(), n = e(this).data("section"), n && l.slidenav_accordion.open(n)
            },
            search_trigger_click: function(e) {
                a.elements.body.hasClass("search-is-open") ? (a.elements.body.removeClass("search-is-open"), c.searchbox.blur().fadeOut(100)) : (a.elements.body.addClass("search-is-open"), c.searchbox.fadeIn(200, function() {
                    c.searchbox.focus()
                })), h.track_header_click("Search")
            },
            search_keypress: function(e) {
                if (e.which == 13) {
                    var t = encodeURI(c.searchbox.val());
                    window.location = "https://www.google.com/#q=" + t + "+site:www.good.is"
                }
            },
            social_mouseenter: function(t) {
                h.load_social(e(this))
            },
            social_click: function(t) {
                h.load_social(e(this))
            },
            nav_link_click: function() {
                h.track_header_click(e(this).data("target"))
            },
            community_link_click: function() {
                h.track_header_click("Community")
            },
            logo_click: function() {
                h.track_header_click("Logo")
            },
            sponsor_img_click: function() {
                h.track_header_click("Sponsor")
            },
            iframe_hover_check: function() {
                l.iframe_hover.fb ? h.track_header_click("FB Like") : l.iframe_hover.twitter && h.track_header_click("Tweet")
            },
            nag_copy_url_click: function() {
                f.track("Share Content", {
                    target: "Copy URL",
                    location: "Scroll Bottom"
                })
            }
        }, h.init()
    };
    return o
}), define("frontend/HeaderVerticals", ["jquery", "frontend/globals", "frontend/Analytics"], function(e, t, n) {
    var r = function(r) {
        var i = this,
            s,
            o,
            u,
            a,
            f,
            l,
            c,
            h;
        s = e.extend({
            $e: null,
            selector: ""
        }, r), o = t(), u = n(), f = {
            name: "HeaderVerticals",
            $e: s.$e || e(s.selector),
            inasswith_window_visible: !1
        }, l = {
            inasswith_container: f.$e.find(".js-inasswith-container"),
            inasswith_trigger: f.$e.find(".js-inasswith-trigger"),
            inasswith_window: f.$e.find(".js-inasswith-window"),
            inasswith_close: f.$e.find(".js-inasswith-window-close"),
            homepage_verticals_abovethefold_ad: f.$e.find("#ad_homepage_verticals_abovethefold"),
            back_to_good_is: f.$e.find("#back_to_good_is"),
            main_logo: f.$e.find("#main_logo"),
            sponsor_logo: f.$e.find("#sponsor_logo")
        }, c = {
            init: function() {
                if (l.inasswith_window.length > 0) {
                    l.inasswith_window.addClass("not-for-phone");
                    var e = l.inasswith_window.clone().addClass("for-phone").removeClass("not-for-phone");
                    l.inasswith_container.after(e)
                }
                l.inasswith_window = f.$e.find(".js-inasswith-window"), l.inasswith_close = f.$e.find(".js-inasswith-window-close"), l.inasswith_trigger.on("click", h.inasswith_trigger_click), l.inasswith_close.on("click", h.inasswith_close_click), l.back_to_good_is.on("click", h.back_to_good_is_click), l.main_logo.on("click", h.main_logo_click), l.sponsor_logo.on("click", h.sponsor_logo_click)
            },
            show_inasswith_window: function() {
                l.inasswith_window.fadeIn(200), f.inasswith_window_visible = !0
            },
            hide_inasswith_window: function() {
                l.inasswith_window.fadeOut(200, function() {
                    l.inasswith_window.css("display", "none")
                }), f.inasswith_window_visible = !1
            },
            track_header_click: function(e) {
                u.track("Header Item Click", {
                    target: e
                })
            }
        }, h = {
            inasswith_trigger_click: function() {
                f.inasswith_window_visible ? c.hide_inasswith_window() : c.show_inasswith_window(), c.track_header_click("in association with")
            },
            inasswith_close_click: function() {
                c.hide_inasswith_window()
            },
            back_to_good_is_click: function() {
                c.track_header_click("back to good.is")
            },
            main_logo_click: function() {
                c.track_header_click("vertical logo")
            },
            sponsor_logo_click: function() {
                c.track_header_click("sponsor logo")
            }
        }, c.init()
    };
    return r
}), define("frontend/Sharing", ["jquery", "frontend/globals", "frontend/Analytics"], function(e, t, n) {
    var r = function(r) {
        var i = this,
            s,
            o,
            u,
            a,
            f,
            l,
            c;
        s = e.extend({
            $e: null,
            selector: "",
            popup_width: 626,
            popup_height: 436
        }, r), o = t(), u = n(), a = {
            name: "Sharing",
            $e: s.$e || e(s.selector),
            og: {}
        }, f = {}, l = {
            init: function() {
                a.og = l.get_og_data(), a.og.url || (console.warn("Sharing > Missing og:url. Falling back to window.location.href"), a.og.url = window.location.href), a.$e.on("click", "[data-share]", c.share_click), a.$e.on("click", "[data-share-image]", c.share_image_click)
            },
            get_og_data: function() {
                var t = {};
                return e('meta[property*="og:"]').each(function() {
                    var n,
                        r,
                        i;
                    n = e(this), r = n.attr("property").split("og:")[1], i = n.attr("content"), t[r] = i
                }), t
            },
            open_dialog: function(e) {
                window.open(e, "share_" + (new Date).getTime(), "width=" + s.popup_width + ", height=" + s.popup_height)
            },
            share_on_facebook: function(e) {
                e.data("share-location") ? l.open_dialog("https://www.facebook.com/sharer/sharer.php?u=" + a.og.url + encodeURIComponent((a.og.url.indexOf("?") === -1 ? "?" : "&") + "sid=ssf" + Math.floor(Math.random() * 1e6) + e.data("share-location"))) : l.open_dialog("https://www.facebook.com/sharer/sharer.php?u=" + a.og.url), platform = e.data("share"), l.send_analytics(e, "Facebook")
            },
            share_on_twitter: function(e) {
                var t,
                    n,
                    r,
                    i = e.data();
                n = a.og.url.replace("http://", "").replace("https://", ""), t = "https://twitter.com/share?url=none", r = i.text || a.og.title, r && (t += "&text=" + encodeURIComponent(r.substring(0, 113)) + (r.length > 113 ? "..." : "")), n && (t += "%20" + n), e.data("share-location") && (t += encodeURIComponent((n.indexOf("?") === -1 ? "?" : "&") + "sid=sst" + Math.floor(Math.random() * 1e6) + e.data("share-location"))), l.open_dialog(t), l.send_analytics(e, "Twitter")
            },
            share_on_linkedin: function(e) {
                var t = "http://www.linkedin.com/shareArticle?mini=true&url=" + encodeURIComponent(a.og.url);
                a.og.title && "&title=" + encodeURIComponent(a.og.title), a.og.description && (t += "&summary=" + encodeURIComponent(a.og.description)), l.open_dialog(t), l.send_analytics(e, "LinkedIn")
            },
            share_on_google_plus: function(e) {
                l.open_dialog("https://plus.google.com/share?url=" + a.og.url), l.send_analytics(e, "Google Plus")
            },
            share_on_stumbleupon: function(e) {
                l.open_dialog("http://www.stumbleupon.com/submit?url=" + a.og.url), l.send_analytics(e, "StumbleUpon")
            },
            share_image_on_pinterest: function(e) {
                var t,
                    n,
                    r = e.data();
                n = r.imageUrl || o.properties.share_image_url, t = "http://www.pinterest.com/pin/create/button/?url=" + encodeURIComponent(a.og.url), t += "&media=" + encodeURIComponent(n), l.open_dialog(t), l.send_analytics(e, "Pinterest")
            },
            share_image_on_tumblr: function(e) {
                var t,
                    n,
                    r = e.data();
                n = r.imageUrl || o.properties.share_image_url, t = "http://www.tumblr.com/share/photo?source=" + encodeURIComponent(n), t += "&clickthru=" + encodeURIComponent(a.og.url), l.open_dialog(t), l.send_analytics(e, "Tumblr")
            },
            send_analytics: function(e, t) {
                var n = "Under Headline";
                e.parent(".js-nag-window").length ? n = "Scroll Bottom" : e.parents(".js-fixie-header").length && (n = "Scroll Top"), u.track("Share Content", {
                    target: t,
                    location: n
                })
            }
        }, c = {
            share_click: function(t, n) {
                var r,
                    i;
                r = e(this), i = r.data("share"), i && l["share_on_" + i] && (t.preventDefault(), l["share_on_" + i](r))
            },
            share_image_click: function(t, n) {
                var r,
                    i;
                r = e(this), i = r.data("share-image"), i && l["share_image_on_" + i] && (t.preventDefault(), l["share_image_on_" + i](r))
            }
        }, l.init()
    };
    return r
}), !function(e) {
    "function" == typeof define && define.amd ? define("jquery.form", ["jquery"], e) : e("undefined" != typeof jQuery ? jQuery : window.Zepto)
}(function(e) {
    function t(t) {
        var n = t.data;
        t.isDefaultPrevented() || (t.preventDefault(), e(t.target).ajaxSubmit(n))
    }
    function n(t) {
        var n = t.target,
            r = e(n);
        if (!r.is("[type=submit],[type=image]")) {
            var i = r.closest("[type=submit]");
            if (0 === i.length)
                return;
            n = i[0]
        }
        var s = this;
        if (s.clk = n, "image" == n.type)
            if (void 0 !== t.offsetX)
                s.clk_x = t.offsetX, s.clk_y = t.offsetY;
            else if ("function" == typeof e.fn.offset) {
                var o = r.offset();
                s.clk_x = t.pageX - o.left, s.clk_y = t.pageY - o.top
            } else
                s.clk_x = t.pageX - n.offsetLeft, s.clk_y = t.pageY - n.offsetTop;
        setTimeout(function() {
            s.clk = s.clk_x = s.clk_y = null
        }, 100)
    }
    function r() {
        if (e.fn.ajaxSubmit.debug) {
            var t = "[jquery.form] " + Array.prototype.join.call(arguments, "");
            window.console && window.console.log ? window.console.log(t) : window.opera && window.opera.postError && window.opera.postError(t)
        }
    }
    var i = {};
    i.fileapi = void 0 !== e("<input type='file'/>").get(0).files, i.formdata = void 0 !== window.FormData;
    var s = !!e.fn.prop;
    e.fn.attr2 = function() {
        if (!s)
            return this.attr.apply(this, arguments);
        var e = this.prop.apply(this, arguments);
        return e && e.jquery || "string" == typeof e ? e : this.attr.apply(this, arguments)
    }, e.fn.ajaxSubmit = function(t) {
        function n(n) {
            var r,
                i,
                s = e.param(n, t.traditional).split("&"),
                o = s.length,
                u = [];
            for (r = 0; o > r; r++)
                s[r] = s[r].replace(/\+/g, " "), i = s[r].split("="), u.push([decodeURIComponent(i[0]), decodeURIComponent(i[1])]);
            return u
        }
        function o(r) {
            for (var i = new FormData, s = 0; s < r.length; s++)
                i.append(r[s].name, r[s].value);
            if (t.extraData) {
                var o = n(t.extraData);
                for (s = 0; s < o.length; s++)
                    o[s] && i.append(o[s][0], o[s][1])
            }
            t.data = null;
            var u = e.extend(!0, {}, e.ajaxSettings, t, {
                contentType: !1,
                processData: !1,
                cache: !1,
                type: f || "POST"
            });
            t.uploadProgress && (u.xhr = function() {
                var n = e.ajaxSettings.xhr();
                return n.upload && n.upload.addEventListener("progress", function(e) {
                    var n = 0,
                        r = e.loaded || e.position,
                        i = e.total;
                    e.lengthComputable && (n = Math.ceil(r / i * 100)), t.uploadProgress(e, r, i, n)
                }, !1), n
            }), u.data = null;
            var a = u.beforeSend;
            return u.beforeSend = function(e, n) {
                n.data = t.formData ? t.formData : i, a && a.call(this, e, n)
            }, e.ajax(u)
        }
        function u(n) {
            function i(e) {
                var t = null;
                try {
                    e.contentWindow && (t = e.contentWindow.document)
                } catch (n) {
                    r("cannot get iframe.contentWindow document: " + n)
                }
                if (t)
                    return t;
                try {
                    t = e.contentDocument ? e.contentDocument : e.document
                } catch (n) {
                    r("cannot get iframe.contentDocument: " + n), t = e.document
                }
                return t
            }
            function o() {
                function t() {
                    try {
                        var e = i(y).readyState;
                        r("state = " + e), e && "uninitialized" == e.toLowerCase() && setTimeout(t, 50)
                    } catch (n) {
                        r("Server abort: ", n, " (", n.name, ")"), u(k), x && clearTimeout(x), x = void 0
                    }
                }
                var n = h.attr2("target"),
                    s = h.attr2("action"),
                    o = "multipart/form-data",
                    l = h.attr("enctype") || h.attr("encoding") || o;
                T.setAttribute("target", v), (!f || /post/i.test(f)) && T.setAttribute("method", "POST"), s != p.url && T.setAttribute("action", p.url), p.skipEncodingOverride || f && !/post/i.test(f) || h.attr({
                    encoding: "multipart/form-data",
                    enctype: "multipart/form-data"
                }), p.timeout && (x = setTimeout(function() {
                    S = !0, u(C)
                }, p.timeout));
                var c = [];
                try {
                    if (p.extraData)
                        for (var d in p.extraData)
                            p.extraData.hasOwnProperty(d) && c.push(e.isPlainObject(p.extraData[d]) && p.extraData[d].hasOwnProperty("name") && p.extraData[d].hasOwnProperty("value") ? e('<input type="hidden" name="' + p.extraData[d].name + '">').val(p.extraData[d].value).appendTo(T)[0] : e('<input type="hidden" name="' + d + '">').val(p.extraData[d]).appendTo(T)[0]);
                    p.iframeTarget || g.appendTo("body"), y.attachEvent ? y.attachEvent("onload", u) : y.addEventListener("load", u, !1), setTimeout(t, 15);
                    try {
                        T.submit()
                    } catch (m) {
                        var b = document.createElement("form").submit;
                        b.apply(T)
                    }
                } finally {
                    T.setAttribute("action", s), T.setAttribute("enctype", l), n ? T.setAttribute("target", n) : h.removeAttr("target"), e(c).remove()
                }
            }
            function u(t) {
                if (!b.aborted && !_) {
                    if (M = i(y), M || (r("cannot access response document"), t = k), t === C && b)
                        return b.abort("timeout"), void N.reject(b, "timeout");
                    if (t == k && b)
                        return b.abort("server abort"), void N.reject(b, "error", "server abort");
                    if (M && M.location.href != p.iframeSrc || S) {
                        y.detachEvent ? y.detachEvent("onload", u) : y.removeEventListener("load", u, !1);
                        var n,
                            s = "success";
                        try {
                            if (S)
                                throw "timeout";
                            var o = "xml" == p.dataType || M.XMLDocument || e.isXMLDoc(M);
                            if (r("isXml=" + o), !o && window.opera && (null === M.body || !M.body.innerHTML) && --D)
                                return r("requeing onLoad callback, DOM not available"), void setTimeout(u, 250);
                            var f = M.body ? M.body : M.documentElement;
                            b.responseText = f ? f.innerHTML : null, b.responseXML = M.XMLDocument ? M.XMLDocument : M, o && (p.dataType = "xml"), b.getResponseHeader = function(e) {
                                var t = {
                                    "content-type": p.dataType
                                };
                                return t[e.toLowerCase()]
                            }, f && (b.status = Number(f.getAttribute("status")) || b.status, b.statusText = f.getAttribute("statusText") || b.statusText);
                            var l = (p.dataType || "").toLowerCase(),
                                c = /(json|script|text)/.test(l);
                            if (c || p.textarea) {
                                var h = M.getElementsByTagName("textarea")[0];
                                if (h)
                                    b.responseText = h.value, b.status = Number(h.getAttribute("status")) || b.status, b.statusText = h.getAttribute("statusText") || b.statusText;
                                else if (c) {
                                    var v = M.getElementsByTagName("pre")[0],
                                        m = M.getElementsByTagName("body")[0];
                                    v ? b.responseText = v.textContent ? v.textContent : v.innerText : m && (b.responseText = m.textContent ? m.textContent : m.innerText)
                                }
                            } else
                                "xml" == l && !b.responseXML && b.responseText && (b.responseXML = P(b.responseText));
                            try {
                                O = B(b, l, p)
                            } catch (w) {
                                s = "parsererror", b.error = n = w || s
                            }
                        } catch (w) {
                            r("error caught: ", w), s = "error", b.error = n = w || s
                        }
                        b.aborted && (r("upload aborted"), s = null), b.status && (s = b.status >= 200 && b.status < 300 || 304 === b.status ? "success" : "error"), "success" === s ? (p.success && p.success.call(p.context, O, "success", b), N.resolve(b.responseText, "success", b), d && e.event.trigger("ajaxSuccess", [b, p])) : s && (void 0 === n && (n = b.statusText), p.error && p.error.call(p.context, b, s, n), N.reject(b, "error", n), d && e.event.trigger("ajaxError", [b, p, n])), d && e.event.trigger("ajaxComplete", [b, p]), d && !--e.active && e.event.trigger("ajaxStop"), p.complete && p.complete.call(p.context, b, s), _ = !0, p.timeout && clearTimeout(x), setTimeout(function() {
                            p.iframeTarget ? g.attr("src", p.iframeSrc) : g.remove(), b.responseXML = null
                        }, 100)
                    }
                }
            }
            var l,
                c,
                p,
                d,
                v,
                g,
                y,
                b,
                w,
                E,
                S,
                x,
                T = h[0],
                N = e.Deferred();
            if (N.abort = function(e) {
                b.abort(e)
            }, n)
                for (c = 0; c < m.length; c++)
                    l = e(m[c]), s ? l.prop("disabled", !1) : l.removeAttr("disabled");
            if (p = e.extend(!0, {}, e.ajaxSettings, t), p.context = p.context || p, v = "jqFormIO" + (new Date).getTime(), p.iframeTarget ? (g = e(p.iframeTarget), E = g.attr2("name"), E ? v = E : g.attr2("name", v)) : (g = e('<iframe name="' + v + '" src="' + p.iframeSrc + '" />'), g.css({
                position: "absolute",
                top: "-1000px",
                left: "-1000px"
            })), y = g[0], b = {
                aborted: 0,
                responseText: null,
                responseXML: null,
                status: 0,
                statusText: "n/a",
                getAllResponseHeaders: function() {},
                getResponseHeader: function() {},
                setRequestHeader: function() {},
                abort: function(t) {
                    var n = "timeout" === t ? "timeout" : "aborted";
                    r("aborting upload... " + n), this.aborted = 1;
                    try {
                        y.contentWindow.document.execCommand && y.contentWindow.document.execCommand("Stop")
                    } catch (i) {}
                    g.attr("src", p.iframeSrc), b.error = n, p.error && p.error.call(p.context, b, n, t), d && e.event.trigger("ajaxError", [b, p, n]), p.complete && p.complete.call(p.context, b, n)
                }
            }, d = p.global, d && 0 === e.active++ && e.event.trigger("ajaxStart"), d && e.event.trigger("ajaxSend", [b, p]), p.beforeSend && p.beforeSend.call(p.context, b, p) === !1)
                return p.global && e.active--, N.reject(), N;
            if (b.aborted)
                return N.reject(), N;
            w = T.clk, w && (E = w.name, E && !w.disabled && (p.extraData = p.extraData || {}, p.extraData[E] = w.value, "image" == w.type && (p.extraData[E + ".x"] = T.clk_x, p.extraData[E + ".y"] = T.clk_y)));
            var C = 1,
                k = 2,
                L = e("meta[name=csrf-token]").attr("content"),
                A = e("meta[name=csrf-param]").attr("content");
            A && L && (p.extraData = p.extraData || {}, p.extraData[A] = L), p.forceSync ? o() : setTimeout(o, 10);
            var O,
                M,
                _,
                D = 50,
                P = e.parseXML || function(e, t) {
                    return window.ActiveXObject ? (t = new ActiveXObject("Microsoft.XMLDOM"), t.async = "false", t.loadXML(e)) : t = (new DOMParser).parseFromString(e, "text/xml"), t && t.documentElement && "parsererror" != t.documentElement.nodeName ? t : null
                },
                H = e.parseJSON || function(e) {
                    return window.eval("(" + e + ")")
                },
                B = function(t, n, r) {
                    var i = t.getResponseHeader("content-type") || "",
                        s = "xml" === n || !n && i.indexOf("xml") >= 0,
                        o = s ? t.responseXML : t.responseText;
                    return s && "parsererror" === o.documentElement.nodeName && e.error && e.error("parsererror"), r && r.dataFilter && (o = r.dataFilter(o, n)), "string" == typeof o && ("json" === n || !n && i.indexOf("json") >= 0 ? o = H(o) : ("script" === n || !n && i.indexOf("javascript") >= 0) && e.globalEval(o)), o
                };
            return N
        }
        if (!this.length)
            return r("ajaxSubmit: skipping submit process - no element selected"), this;
        var f,
            l,
            c,
            h = this;
        "function" == typeof t ? t = {
            success: t
        } : void 0 === t && (t = {}), f = t.type || this.attr2("method"), l = t.url || this.attr2("action"), c = "string" == typeof l ? e.trim(l) : "", c = c || window.location.href || "", c && (c = (c.match(/^([^#]+)/) || [])[1]), t = e.extend(!0, {
            url: c,
            success: e.ajaxSettings.success,
            type: f || e.ajaxSettings.type,
            iframeSrc: /^https/i.test(window.location.href || "") ? "javascript:false" : "about:blank"
        }, t);
        var p = {};
        if (this.trigger("form-pre-serialize", [this, t, p]), p.veto)
            return r("ajaxSubmit: submit vetoed via form-pre-serialize trigger"), this;
        if (t.beforeSerialize && t.beforeSerialize(this, t) === !1)
            return r("ajaxSubmit: submit aborted via beforeSerialize callback"), this;
        var d = t.traditional;
        void 0 === d && (d = e.ajaxSettings.traditional);
        var v,
            m = [],
            g = this.formToArray(t.semantic, m);
        if (t.data && (t.extraData = t.data, v = e.param(t.data, d)), t.beforeSubmit && t.beforeSubmit(g, this, t) === !1)
            return r("ajaxSubmit: submit aborted via beforeSubmit callback"), this;
        if (this.trigger("form-submit-validate", [g, this, t, p]), p.veto)
            return r("ajaxSubmit: submit vetoed via form-submit-validate trigger"), this;
        var y = e.param(g, d);
        v && (y = y ? y + "&" + v : v), "GET" == t.type.toUpperCase() ? (t.url += (t.url.indexOf("?") >= 0 ? "&" : "?") + y, t.data = null) : t.data = y;
        var b = [];
        if (t.resetForm && b.push(function() {
            h.resetForm()
        }), t.clearForm && b.push(function() {
            h.clearForm(t.includeHidden)
        }), !t.dataType && t.target) {
            var w = t.success || function() {};
            b.push(function(n) {
                var r = t.replaceTarget ? "replaceWith" : "html";
                e(t.target)[r](n).each(w, arguments)
            })
        } else
            t.success && b.push(t.success);
        if (t.success = function(e, n, r) {
            for (var i = t.context || this, s = 0, o = b.length; o > s; s++)
                b[s].apply(i, [e, n, r || h, h])
        }, t.error) {
            var E = t.error;
            t.error = function(e, n, r) {
                var i = t.context || this;
                E.apply(i, [e, n, r, h])
            }
        }
        if (t.complete) {
            var S = t.complete;
            t.complete = function(e, n) {
                var r = t.context || this;
                S.apply(r, [e, n, h])
            }
        }
        var x = e("input[type=file]:enabled", this).filter(function() {
                return "" !== e(this).val()
            }),
            T = x.length > 0,
            N = "multipart/form-data",
            C = h.attr("enctype") == N || h.attr("encoding") == N,
            k = i.fileapi && i.formdata;
        r("fileAPI :" + k);
        var L,
            A = (T || C) && !k;
        t.iframe !== !1 && (t.iframe || A) ? t.closeKeepAlive ? e.get(t.closeKeepAlive, function() {
            L = u(g)
        }) : L = u(g) : L = (T || C) && k ? o(g) : e.ajax(t), h.removeData("jqxhr").data("jqxhr", L);
        for (var O = 0; O < m.length; O++)
            m[O] = null;
        return this.trigger("form-submit-notify", [this, t]), this
    }, e.fn.ajaxForm = function(i) {
        if (i = i || {}, i.delegation = i.delegation && e.isFunction(e.fn.on), !i.delegation && 0 === this.length) {
            var s = {
                s: this.selector,
                c: this.context
            };
            return !e.isReady && s.s ? (r("DOM not ready, queuing ajaxForm"), e(function() {
                e(s.s, s.c).ajaxForm(i)
            }), this) : (r("terminating; zero elements found by selector" + (e.isReady ? "" : " (DOM not ready)")), this)
        }
        return i.delegation ? (e(document).off("submit.form-plugin", this.selector, t).off("click.form-plugin", this.selector, n).on("submit.form-plugin", this.selector, i, t).on("click.form-plugin", this.selector, i, n), this) : this.ajaxFormUnbind().bind("submit.form-plugin", i, t).bind("click.form-plugin", i, n)
    }, e.fn.ajaxFormUnbind = function() {
        return this.unbind("submit.form-plugin click.form-plugin")
    }, e.fn.formToArray = function(t, n) {
        var r = [];
        if (0 === this.length)
            return r;
        var s,
            o = this[0],
            u = this.attr("id"),
            a = t ? o.getElementsByTagName("*") : o.elements;
        if (a && !/MSIE [678]/.test(navigator.userAgent) && (a = e(a).get()), u && (s = e(':input[form="' + u + '"]').get(), s.length && (a = (a || []).concat(s))), !a || !a.length)
            return r;
        var f,
            l,
            c,
            h,
            p,
            d,
            v;
        for (f = 0, d = a.length; d > f; f++)
            if (p = a[f], c = p.name, c && !p.disabled)
                if (t && o.clk && "image" == p.type)
                    o.clk == p && (r.push({
                        name: c,
                        value: e(p).val(),
                        type: p.type
                    }), r.push({
                        name: c + ".x",
                        value: o.clk_x
                    }, {
                        name: c + ".y",
                        value: o.clk_y
                    }));
                else if (h = e.fieldValue(p, !0), h && h.constructor == Array)
                    for (n && n.push(p), l = 0, v = h.length; v > l; l++)
                        r.push({
                            name: c,
                            value: h[l]
                        });
                else if (i.fileapi && "file" == p.type) {
                    n && n.push(p);
                    var m = p.files;
                    if (m.length)
                        for (l = 0; l < m.length; l++)
                            r.push({
                                name: c,
                                value: m[l],
                                type: p.type
                            });
                    else
                        r.push({
                            name: c,
                            value: "",
                            type: p.type
                        })
                } else
                    null !== h && "undefined" != typeof h && (n && n.push(p), r.push({
                        name: c,
                        value: h,
                        type: p.type,
                        required: p.required
                    }));
        if (!t && o.clk) {
            var g = e(o.clk),
                y = g[0];
            c = y.name, c && !y.disabled && "image" == y.type && (r.push({
                name: c,
                value: g.val()
            }), r.push({
                name: c + ".x",
                value: o.clk_x
            }, {
                name: c + ".y",
                value: o.clk_y
            }))
        }
        return r
    }, e.fn.formSerialize = function(t) {
        return e.param(this.formToArray(t))
    }, e.fn.fieldSerialize = function(t) {
        var n = [];
        return this.each(function() {
            var r = this.name;
            if (r) {
                var i = e.fieldValue(this, t);
                if (i && i.constructor == Array)
                    for (var s = 0, o = i.length; o > s; s++)
                        n.push({
                            name: r,
                            value: i[s]
                        });
                else
                    null !== i && "undefined" != typeof i && n.push({
                        name: this.name,
                        value: i
                    })
            }
        }), e.param(n)
    }, e.fn.fieldValue = function(t) {
        for (var n = [], r = 0, i = this.length; i > r; r++) {
            var s = this[r],
                o = e.fieldValue(s, t);
            null === o || "undefined" == typeof o || o.constructor == Array && !o.length || (o.constructor == Array ? e.merge(n, o) : n.push(o))
        }
        return n
    }, e.fieldValue = function(t, n) {
        var r = t.name,
            i = t.type,
            s = t.tagName.toLowerCase();
        if (void 0 === n && (n = !0), n && (!r || t.disabled || "reset" == i || "button" == i || ("checkbox" == i || "radio" == i) && !t.checked || ("submit" == i || "image" == i) && t.form && t.form.clk != t || "select" == s && -1 == t.selectedIndex))
            return null;
        if ("select" == s) {
            var o = t.selectedIndex;
            if (0 > o)
                return null;
            for (var u = [], a = t.options, f = "select-one" == i, l = f ? o + 1 : a.length, c = f ? o : 0; l > c; c++) {
                var h = a[c];
                if (h.selected) {
                    var p = h.value;
                    if (p || (p = h.attributes && h.attributes.value && !h.attributes.value.specified ? h.text : h.value), f)
                        return p;
                    u.push(p)
                }
            }
            return u
        }
        return e(t).val()
    }, e.fn.clearForm = function(t) {
        return this.each(function() {
            e("input,select,textarea", this).clearFields(t)
        })
    }, e.fn.clearFields = e.fn.clearInputs = function(t) {
        var n = /^(?:color|date|datetime|email|month|number|password|range|search|tel|text|time|url|week)$/i;
        return this.each(function() {
            var r = this.type,
                i = this.tagName.toLowerCase();
            n.test(r) || "textarea" == i ? this.value = "" : "checkbox" == r || "radio" == r ? this.checked = !1 : "select" == i ? this.selectedIndex = -1 : "file" == r ? /MSIE/.test(navigator.userAgent) ? e(this).replaceWith(e(this).clone(!0)) : e(this).val("") : t && (t === !0 && /hidden/.test(r) || "string" == typeof t && e(this).is(t)) && (this.value = "")
        })
    }, e.fn.resetForm = function() {
        return this.each(function() {
            ("function" == typeof this.reset || "object" == typeof this.reset && !this.reset.nodeType) && this.reset()
        })
    }, e.fn.enable = function(e) {
        return void 0 === e && (e = !0), this.each(function() {
            this.disabled = !e
        })
    }, e.fn.selected = function(t) {
        return void 0 === t && (t = !0), this.each(function() {
            var n = this.type;
            if ("checkbox" == n || "radio" == n)
                this.checked = t;
            else if ("option" == this.tagName.toLowerCase()) {
                var r = e(this).parent("select");
                t && r[0] && "select-one" == r[0].type && r.find("option").selected(!1), this.selected = t
            }
        })
    }, e.fn.ajaxSubmit.debug = !1
}), !function(e) {
    "function" == typeof define && define.amd ? define("jquery.validate", ["jquery"], e) : e(jQuery)
}(function(e) {
    e.extend(e.fn, {
        validate: function(t) {
            if (!this.length)
                return void (t && t.debug && window.console && console.warn("Nothing selected, can't validate, returning nothing."));
            var n = e.data(this[0], "validator");
            return n ? n : (this.attr("novalidate", "novalidate"), n = new e.validator(t, this[0]), e.data(this[0], "validator", n), n.settings.onsubmit && (this.validateDelegate(":submit", "click", function(t) {
                n.settings.submitHandler && (n.submitButton = t.target), e(t.target).hasClass("cancel") && (n.cancelSubmit = !0), void 0 !== e(t.target).attr("formnovalidate") && (n.cancelSubmit = !0)
            }), this.submit(function(t) {
                function r() {
                    var r,
                        i;
                    return n.settings.submitHandler ? (n.submitButton && (r = e("<input type='hidden'/>").attr("name", n.submitButton.name).val(e(n.submitButton).val()).appendTo(n.currentForm)), i = n.settings.submitHandler.call(n, n.currentForm, t), n.submitButton && r.remove(), void 0 !== i ? i : !1) : !0
                }
                return n.settings.debug && t.preventDefault(), n.cancelSubmit ? (n.cancelSubmit = !1, r()) : n.form() ? n.pendingRequest ? (n.formSubmitted = !0, !1) : r() : (n.focusInvalid(), !1)
            })), n)
        },
        valid: function() {
            var t,
                n;
            return e(this[0]).is("form") ? t = this.validate().form() : (t = !0, n = e(this[0].form).validate(), this.each(function() {
                t = n.element(this) && t
            })), t
        },
        removeAttrs: function(t) {
            var n = {},
                r = this;
            return e.each(t.split(/\s/), function(e, t) {
                n[t] = r.attr(t), r.removeAttr(t)
            }), n
        },
        rules: function(t, n) {
            var r,
                i,
                s,
                o,
                u,
                f,
                l = this[0];
            if (t)
                switch (r = e.data(l.form, "validator").settings, i = r.rules, s = e.validator.staticRules(l), t) {
                case "add":
                    e.extend(s, e.validator.normalizeRule(n)), delete s.messages, i[l.name] = s, n.messages && (r.messages[l.name] = e.extend(r.messages[l.name], n.messages));
                    break;
                case "remove":
                    return n ? (f = {}, e.each(n.split(/\s/), function(t, n) {
                        f[n] = s[n], delete s[n], "required" === n && e(l).removeAttr("aria-required")
                    }), f) : (delete i[l.name], s)
                }
            return o = e.validator.normalizeRules(e.extend({}, e.validator.classRules(l), e.validator.attributeRules(l), e.validator.dataRules(l), e.validator.staticRules(l)), l), o.required && (u = o.required, delete o.required, o = e.extend({
                required: u
            }, o), e(l).attr("aria-required", "true")), o.remote && (u = o.remote, delete o.remote, o = e.extend(o, {
                remote: u
            })), o
        }
    }), e.extend(e.expr[":"], {
        blank: function(t) {
            return !e.trim("" + e(t).val())
        },
        filled: function(t) {
            return !!e.trim("" + e(t).val())
        },
        unchecked: function(t) {
            return !e(t).prop("checked")
        }
    }), e.validator = function(t, n) {
        this.settings = e.extend(!0, {}, e.validator.defaults, t), this.currentForm = n, this.init()
    }, e.validator.format = function(t, n) {
        return 1 === arguments.length ? function() {
            var n = e.makeArray(arguments);
            return n.unshift(t), e.validator.format.apply(this, n)
        } : (arguments.length > 2 && n.constructor !== Array && (n = e.makeArray(arguments).slice(1)), n.constructor !== Array && (n = [n]), e.each(n, function(e, n) {
            t = t.replace(new RegExp("\\{" + e + "\\}", "g"), function() {
                return n
            })
        }), t)
    }, e.extend(e.validator, {
        defaults: {
            messages: {},
            groups: {},
            rules: {},
            errorClass: "error",
            validClass: "valid",
            errorElement: "label",
            focusCleanup: !1,
            focusInvalid: !0,
            errorContainer: e([]),
            errorLabelContainer: e([]),
            onsubmit: !0,
            ignore: ":hidden",
            ignoreTitle: !1,
            onfocusin: function(e) {
                this.lastActive = e, this.settings.focusCleanup && (this.settings.unhighlight && this.settings.unhighlight.call(this, e, this.settings.errorClass, this.settings.validClass), this.hideThese(this.errorsFor(e)))
            },
            onfocusout: function(e) {
                this.checkable(e) || !(e.name in this.submitted) && this.optional(e) || this.element(e)
            },
            onkeyup: function(e, t) {
                (9 !== t.which || "" !== this.elementValue(e)) && (e.name in this.submitted || e === this.lastElement) && this.element(e)
            },
            onclick: function(e) {
                e.name in this.submitted ? this.element(e) : e.parentNode.name in this.submitted && this.element(e.parentNode)
            },
            highlight: function(t, n, r) {
                "radio" === t.type ? this.findByName(t.name).addClass(n).removeClass(r) : e(t).addClass(n).removeClass(r)
            },
            unhighlight: function(t, n, r) {
                "radio" === t.type ? this.findByName(t.name).removeClass(n).addClass(r) : e(t).removeClass(n).addClass(r)
            }
        },
        setDefaults: function(t) {
            e.extend(e.validator.defaults, t)
        },
        messages: {
            required: "This field is required.",
            remote: "Please fix this field.",
            email: "Please enter a valid email address.",
            url: "Please enter a valid URL.",
            date: "Please enter a valid date.",
            dateISO: "Please enter a valid date ( ISO ).",
            number: "Please enter a valid number.",
            digits: "Please enter only digits.",
            creditcard: "Please enter a valid credit card number.",
            equalTo: "Please enter the same value again.",
            maxlength: e.validator.format("Please enter no more than {0} characters."),
            minlength: e.validator.format("Please enter at least {0} characters."),
            rangelength: e.validator.format("Please enter a value between {0} and {1} characters long."),
            range: e.validator.format("Please enter a value between {0} and {1}."),
            max: e.validator.format("Please enter a value less than or equal to {0}."),
            min: e.validator.format("Please enter a value greater than or equal to {0}.")
        },
        autoCreateRanges: !1,
        prototype: {
            init: function() {
                function t(t) {
                    var n = e.data(this[0].form, "validator"),
                        r = "on" + t.type.replace(/^validate/, ""),
                        i = n.settings;
                    i[r] && !this.is(i.ignore) && i[r].call(n, this[0], t)
                }
                this.labelContainer = e(this.settings.errorLabelContainer), this.errorContext = this.labelContainer.length && this.labelContainer || e(this.currentForm), this.containers = e(this.settings.errorContainer).add(this.settings.errorLabelContainer), this.submitted = {}, this.valueCache = {}, this.pendingRequest = 0, this.pending = {}, this.invalid = {}, this.reset();
                var n,
                    r = this.groups = {};
                e.each(this.settings.groups, function(t, n) {
                    "string" == typeof n && (n = n.split(/\s/)), e.each(n, function(e, n) {
                        r[n] = t
                    })
                }), n = this.settings.rules, e.each(n, function(t, r) {
                    n[t] = e.validator.normalizeRule(r)
                }), e(this.currentForm).validateDelegate(":text, [type='password'], [type='file'], select, textarea, [type='number'], [type='search'] ,[type='tel'], [type='url'], [type='email'], [type='datetime'], [type='date'], [type='month'], [type='week'], [type='time'], [type='datetime-local'], [type='range'], [type='color'], [type='radio'], [type='checkbox']", "focusin focusout keyup", t).validateDelegate("select, option, [type='radio'], [type='checkbox']", "click", t), this.settings.invalidHandler && e(this.currentForm).bind("invalid-form.validate", this.settings.invalidHandler), e(this.currentForm).find("[required], [data-rule-required], .required").attr("aria-required", "true")
            },
            form: function() {
                return this.checkForm(), e.extend(this.submitted, this.errorMap), this.invalid = e.extend({}, this.errorMap), this.valid() || e(this.currentForm).triggerHandler("invalid-form", [this]), this.showErrors(), this.valid()
            },
            checkForm: function() {
                this.prepareForm();
                for (var e = 0, t = this.currentElements = this.elements(); t[e]; e++)
                    this.check(t[e]);
                return this.valid()
            },
            element: function(t) {
                var n = this.clean(t),
                    r = this.validationTargetFor(n),
                    i = !0;
                return this.lastElement = r, void 0 === r ? delete this.invalid[n.name] : (this.prepareElement(r), this.currentElements = e(r), i = this.check(r) !== !1, i ? delete this.invalid[r.name] : this.invalid[r.name] = !0), e(t).attr("aria-invalid", !i), this.numberOfInvalids() || (this.toHide = this.toHide.add(this.containers)), this.showErrors(), i
            },
            showErrors: function(t) {
                if (t) {
                    e.extend(this.errorMap, t), this.errorList = [];
                    for (var n in t)
                        this.errorList.push({
                            message: t[n],
                            element: this.findByName(n)[0]
                        });
                    this.successList = e.grep(this.successList, function(e) {
                        return !(e.name in t)
                    })
                }
                this.settings.showErrors ? this.settings.showErrors.call(this, this.errorMap, this.errorList) : this.defaultShowErrors()
            },
            resetForm: function() {
                e.fn.resetForm && e(this.currentForm).resetForm(), this.submitted = {}, this.lastElement = null, this.prepareForm(), this.hideErrors(), this.elements().removeClass(this.settings.errorClass).removeData("previousValue").removeAttr("aria-invalid")
            },
            numberOfInvalids: function() {
                return this.objectLength(this.invalid)
            },
            objectLength: function(e) {
                var t,
                    n = 0;
                for (t in e)
                    n++;
                return n
            },
            hideErrors: function() {
                this.hideThese(this.toHide)
            },
            hideThese: function(e) {
                e.not(this.containers).text(""), this.addWrapper(e).hide()
            },
            valid: function() {
                return 0 === this.size()
            },
            size: function() {
                return this.errorList.length
            },
            focusInvalid: function() {
                if (this.settings.focusInvalid)
                    try {
                        e(this.findLastActive() || this.errorList.length && this.errorList[0].element || []).filter(":visible").focus().trigger("focusin")
                    } catch (t) {}
            },
            findLastActive: function() {
                var t = this.lastActive;
                return t && 1 === e.grep(this.errorList, function(e) {
                        return e.element.name === t.name
                    }).length && t
            },
            elements: function() {
                var t = this,
                    n = {};
                return e(this.currentForm).find("input, select, textarea").not(":submit, :reset, :image, [disabled], [readonly]").not(this.settings.ignore).filter(function() {
                    return !this.name && t.settings.debug && window.console && console.error("%o has no name assigned", this), this.name in n || !t.objectLength(e(this).rules()) ? !1 : (n[this.name] = !0, !0)
                })
            },
            clean: function(t) {
                return e(t)[0]
            },
            errors: function() {
                var t = this.settings.errorClass.split(" ").join(".");
                return e(this.settings.errorElement + "." + t, this.errorContext)
            },
            reset: function() {
                this.successList = [], this.errorList = [], this.errorMap = {}, this.toShow = e([]), this.toHide = e([]), this.currentElements = e([])
            },
            prepareForm: function() {
                this.reset(), this.toHide = this.errors().add(this.containers)
            },
            prepareElement: function(e) {
                this.reset(), this.toHide = this.errorsFor(e)
            },
            elementValue: function(t) {
                var n,
                    r = e(t),
                    i = t.type;
                return "radio" === i || "checkbox" === i ? e("input[name='" + t.name + "']:checked").val() : "number" === i && "undefined" != typeof t.validity ? t.validity.badInput ? !1 : r.val() : (n = r.val(), "string" == typeof n ? n.replace(/\r/g, "") : n)
            },
            check: function(t) {
                t = this.validationTargetFor(this.clean(t));
                var n,
                    r,
                    i,
                    s = e(t).rules(),
                    o = e.map(s, function(e, t) {
                        return t
                    }).length,
                    u = !1,
                    f = this.elementValue(t);
                for (r in s) {
                    i = {
                        method: r,
                        parameters: s[r]
                    };
                    try {
                        if (n = e.validator.methods[r].call(this, f, t, i.parameters), "dependency-mismatch" === n && 1 === o) {
                            u = !0;
                            continue
                        }
                        if (u = !1, "pending" === n)
                            return void (this.toHide = this.toHide.not(this.errorsFor(t)));
                        if (!n)
                            return this.formatAndAdd(t, i), !1
                    } catch (l) {
                        throw this.settings.debug && window.console && console.log("Exception occurred when checking element " + t.id + ", check the '" + i.method + "' method.", l), l
                    }
                }
                if (!u)
                    return this.objectLength(s) && this.successList.push(t), !0
            },
            customDataMessage: function(t, n) {
                return e(t).data("msg" + n.charAt(0).toUpperCase() + n.substring(1).toLowerCase()) || e(t).data("msg")
            },
            customMessage: function(e, t) {
                var n = this.settings.messages[e];
                return n && (n.constructor === String ? n : n[t])
            },
            findDefined: function() {
                for (var e = 0; e < arguments.length; e++)
                    if (void 0 !== arguments[e])
                        return arguments[e];
                return void 0
            },
            defaultMessage: function(t, n) {
                return this.findDefined(this.customMessage(t.name, n), this.customDataMessage(t, n), !this.settings.ignoreTitle && t.title || void 0, e.validator.messages[n], "<strong>Warning: No message defined for " + t.name + "</strong>")
            },
            formatAndAdd: function(t, n) {
                var r = this.defaultMessage(t, n.method),
                    i = /\$?\{(\d+)\}/g;
                "function" == typeof r ? r = r.call(this, n.parameters, t) : i.test(r) && (r = e.validator.format(r.replace(i, "{$1}"), n.parameters)), this.errorList.push({
                    message: r,
                    element: t,
                    method: n.method
                }), this.errorMap[t.name] = r, this.submitted[t.name] = r
            },
            addWrapper: function(e) {
                return this.settings.wrapper && (e = e.add(e.parent(this.settings.wrapper))), e
            },
            defaultShowErrors: function() {
                var e,
                    t,
                    n;
                for (e = 0; this.errorList[e]; e++)
                    n = this.errorList[e], this.settings.highlight && this.settings.highlight.call(this, n.element, this.settings.errorClass, this.settings.validClass), this.showLabel(n.element, n.message);
                if (this.errorList.length && (this.toShow = this.toShow.add(this.containers)), this.settings.success)
                    for (e = 0; this.successList[e]; e++)
                        this.showLabel(this.successList[e]);
                if (this.settings.unhighlight)
                    for (e = 0, t = this.validElements(); t[e]; e++)
                        this.settings.unhighlight.call(this, t[e], this.settings.errorClass, this.settings.validClass);
                this.toHide = this.toHide.not(this.toShow), this.hideErrors(), this.addWrapper(this.toShow).show()
            },
            validElements: function() {
                return this.currentElements.not(this.invalidElements())
            },
            invalidElements: function() {
                return e(this.errorList).map(function() {
                    return this.element
                })
            },
            showLabel: function(t, n) {
                var r,
                    i,
                    s,
                    o = this.errorsFor(t),
                    u = this.idOrName(t),
                    f = e(t).attr("aria-describedby");
                o.length ? (o.removeClass(this.settings.validClass).addClass(this.settings.errorClass), o.html(n)) : (o = e("<" + this.settings.errorElement + ">").attr("id", u + "-error").addClass(this.settings.errorClass).html(n || ""), r = o, this.settings.wrapper && (r = o.hide().show().wrap("<" + this.settings.wrapper + "/>").parent()), this.labelContainer.length ? this.labelContainer.append(r) : this.settings.errorPlacement ? this.settings.errorPlacement(r, e(t)) : r.insertAfter(t), o.is("label") ? o.attr("for", u) : 0 === o.parents("label[for='" + u + "']").length && (s = o.attr("id").replace(/(:|\.|\[|\])/g, "\\$1"), f ? f.match(new RegExp("\\b" + s + "\\b")) || (f += " " + s) : f = s, e(t).attr("aria-describedby", f), i = this.groups[t.name], i && e.each(this.groups, function(t, n) {
                    n === i && e("[name='" + t + "']", this.currentForm).attr("aria-describedby", o.attr("id"))
                }))), !n && this.settings.success && (o.text(""), "string" == typeof this.settings.success ? o.addClass(this.settings.success) : this.settings.success(o, t)), this.toShow = this.toShow.add(o)
            },
            errorsFor: function(t) {
                var n = this.idOrName(t),
                    r = e(t).attr("aria-describedby"),
                    i = "label[for='" + n + "'], label[for='" + n + "'] *";
                return r && (i = i + ", #" + r.replace(/\s+/g, ", #")), this.errors().filter(i)
            },
            idOrName: function(e) {
                return this.groups[e.name] || (this.checkable(e) ? e.name : e.id || e.name)
            },
            validationTargetFor: function(t) {
                return this.checkable(t) && (t = this.findByName(t.name)), e(t).not(this.settings.ignore)[0]
            },
            checkable: function(e) {
                return /radio|checkbox/i.test(e.type)
            },
            findByName: function(t) {
                return e(this.currentForm).find("[name='" + t + "']")
            },
            getLength: function(t, n) {
                switch (n.nodeName.toLowerCase()) {
                case "select":
                    return e("option:selected", n).length;
                case "input":
                    if (this.checkable(n))
                        return this.findByName(n.name).filter(":checked").length
                }
                return t.length
            },
            depend: function(e, t) {
                return this.dependTypes[typeof e] ? this.dependTypes[typeof e](e, t) : !0
            },
            dependTypes: {
                "boolean": function(e) {
                    return e
                },
                string: function(t, n) {
                    return !!e(t, n.form).length
                },
                "function": function(e, t) {
                    return e(t)
                }
            },
            optional: function(t) {
                var n = this.elementValue(t);
                return !e.validator.methods.required.call(this, n, t) && "dependency-mismatch"
            },
            startRequest: function(e) {
                this.pending[e.name] || (this.pendingRequest++, this.pending[e.name] = !0)
            },
            stopRequest: function(t, n) {
                this.pendingRequest--, this.pendingRequest < 0 && (this.pendingRequest = 0), delete this.pending[t.name], n && 0 === this.pendingRequest && this.formSubmitted && this.form() ? (e(this.currentForm).submit(), this.formSubmitted = !1) : !n && 0 === this.pendingRequest && this.formSubmitted && (e(this.currentForm).triggerHandler("invalid-form", [this]), this.formSubmitted = !1)
            },
            previousValue: function(t) {
                return e.data(t, "previousValue") || e.data(t, "previousValue", {
                        old: null,
                        valid: !0,
                        message: this.defaultMessage(t, "remote")
                    })
            }
        },
        classRuleSettings: {
            required: {
                required: !0
            },
            email: {
                email: !0
            },
            url: {
                url: !0
            },
            date: {
                date: !0
            },
            dateISO: {
                dateISO: !0
            },
            number: {
                number: !0
            },
            digits: {
                digits: !0
            },
            creditcard: {
                creditcard: !0
            }
        },
        addClassRules: function(t, n) {
            t.constructor === String ? this.classRuleSettings[t] = n : e.extend(this.classRuleSettings, t)
        },
        classRules: function(t) {
            var n = {},
                r = e(t).attr("class");
            return r && e.each(r.split(" "), function() {
                this in e.validator.classRuleSettings && e.extend(n, e.validator.classRuleSettings[this])
            }), n
        },
        attributeRules: function(t) {
            var n,
                r,
                i = {},
                s = e(t),
                o = t.getAttribute("type");
            for (n in e.validator.methods)
                "required" === n ? (r = t.getAttribute(n), "" === r && (r = !0), r = !!r) : r = s.attr(n), /min|max/.test(n) && (null === o || /number|range|text/.test(o)) && (r = Number(r)), r || 0 === r ? i[n] = r : o === n && "range" !== o && (i[n] = !0);
            return i.maxlength && /-1|2147483647|524288/.test(i.maxlength) && delete i.maxlength, i
        },
        dataRules: function(t) {
            var n,
                r,
                i = {},
                s = e(t);
            for (n in e.validator.methods)
                r = s.data("rule" + n.charAt(0).toUpperCase() + n.substring(1).toLowerCase()), void 0 !== r && (i[n] = r);
            return i
        },
        staticRules: function(t) {
            var n = {},
                r = e.data(t.form, "validator");
            return r.settings.rules && (n = e.validator.normalizeRule(r.settings.rules[t.name]) || {}), n
        },
        normalizeRules: function(t, n) {
            return e.each(t, function(r, i) {
                if (i === !1)
                    return void delete t[r];
                if (i.param || i.depends) {
                    var s = !0;
                    switch (typeof i.depends) {
                    case "string":
                        s = !!e(i.depends, n.form).length;
                        break;
                    case "function":
                        s = i.depends.call(n, n)
                    }
                    s ? t[r] = void 0 !== i.param ? i.param : !0 : delete t[r]
                }
            }), e.each(t, function(r, i) {
                t[r] = e.isFunction(i) ? i(n) : i
            }), e.each(["minlength", "maxlength"], function() {
                t[this] && (t[this] = Number(t[this]))
            }), e.each(["rangelength", "range"], function() {
                var n;
                t[this] && (e.isArray(t[this]) ? t[this] = [Number(t[this][0]), Number(t[this][1])] : "string" == typeof t[this] && (n = t[this].replace(/[\[\]]/g, "").split(/[\s,]+/), t[this] = [Number(n[0]), Number(n[1])]))
            }), e.validator.autoCreateRanges && (null != t.min && null != t.max && (t.range = [t.min, t.max], delete t.min, delete t.max), null != t.minlength && null != t.maxlength && (t.rangelength = [t.minlength, t.maxlength], delete t.minlength, delete t.maxlength)), t
        },
        normalizeRule: function(t) {
            if ("string" == typeof t) {
                var n = {};
                e.each(t.split(/\s/), function() {
                    n[this] = !0
                }), t = n
            }
            return t
        },
        addMethod: function(t, n, r) {
            e.validator.methods[t] = n, e.validator.messages[t] = void 0 !== r ? r : e.validator.messages[t], n.length < 3 && e.validator.addClassRules(t, e.validator.normalizeRule(t))
        },
        methods: {
            required: function(t, n, r) {
                if (!this.depend(r, n))
                    return "dependency-mismatch";
                if ("select" === n.nodeName.toLowerCase()) {
                    var i = e(n).val();
                    return i && i.length > 0
                }
                return this.checkable(n) ? this.getLength(t, n) > 0 : e.trim(t).length > 0
            },
            email: function(e, t) {
                return this.optional(t) || /^[a-zA-Z0-9.!#$%&'*+\/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$/.test(e)
            },
            url: function(e, t) {
                return this.optional(t) || /^(https?|s?ftp):\/\/(((([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(%[\da-f]{2})|[!\$&'\(\)\*\+,;=]|:)*@)?(((\d|[1-9]\d|1\d\d|2[0-4]\d|25[0-5])\.(\d|[1-9]\d|1\d\d|2[0-4]\d|25[0-5])\.(\d|[1-9]\d|1\d\d|2[0-4]\d|25[0-5])\.(\d|[1-9]\d|1\d\d|2[0-4]\d|25[0-5]))|((([a-z]|\d|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(([a-z]|\d|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])*([a-z]|\d|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])))\.)+(([a-z]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(([a-z]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])*([a-z]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])))\.?)(:\d*)?)(\/((([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(%[\da-f]{2})|[!\$&'\(\)\*\+,;=]|:|@)+(\/(([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(%[\da-f]{2})|[!\$&'\(\)\*\+,;=]|:|@)*)*)?)?(\?((([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(%[\da-f]{2})|[!\$&'\(\)\*\+,;=]|:|@)|[\uE000-\uF8FF]|\/|\?)*)?(#((([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(%[\da-f]{2})|[!\$&'\(\)\*\+,;=]|:|@)|\/|\?)*)?$/i.test(e)
            },
            date: function(e, t) {
                return this.optional(t) || !/Invalid|NaN/.test((new Date(e)).toString())
            },
            dateISO: function(e, t) {
                return this.optional(t) || /^\d{4}[\/\-](0?[1-9]|1[012])[\/\-](0?[1-9]|[12][0-9]|3[01])$/.test(e)
            },
            number: function(e, t) {
                return this.optional(t) || /^-?(?:\d+|\d{1,3}(?:,\d{3})+)?(?:\.\d+)?$/.test(e)
            },
            digits: function(e, t) {
                return this.optional(t) || /^\d+$/.test(e)
            },
            creditcard: function(e, t) {
                if (this.optional(t))
                    return "dependency-mismatch";
                if (/[^0-9 \-]+/.test(e))
                    return !1;
                var n,
                    r,
                    i = 0,
                    s = 0,
                    o = !1;
                if (e = e.replace(/\D/g, ""), e.length < 13 || e.length > 19)
                    return !1;
                for (n = e.length - 1; n >= 0; n--)
                    r = e.charAt(n), s = parseInt(r, 10), o && (s *= 2) > 9 && (s -= 9), i += s, o = !o;
                return i % 10 === 0
            },
            minlength: function(t, n, r) {
                var i = e.isArray(t) ? t.length : this.getLength(t, n);
                return this.optional(n) || i >= r
            },
            maxlength: function(t, n, r) {
                var i = e.isArray(t) ? t.length : this.getLength(t, n);
                return this.optional(n) || r >= i
            },
            rangelength: function(t, n, r) {
                var i = e.isArray(t) ? t.length : this.getLength(t, n);
                return this.optional(n) || i >= r[0] && i <= r[1]
            },
            min: function(e, t, n) {
                return this.optional(t) || e >= n
            },
            max: function(e, t, n) {
                return this.optional(t) || n >= e
            },
            range: function(e, t, n) {
                return this.optional(t) || e >= n[0] && e <= n[1]
            },
            equalTo: function(t, n, r) {
                var i = e(r);
                return this.settings.onfocusout && i.unbind(".validate-equalTo").bind("blur.validate-equalTo", function() {
                    e(n).valid()
                }), t === i.val()
            },
            remote: function(t, n, r) {
                if (this.optional(n))
                    return "dependency-mismatch";
                var i,
                    s,
                    o = this.previousValue(n);
                return this.settings.messages[n.name] || (this.settings.messages[n.name] = {}), o.originalMessage = this.settings.messages[n.name].remote, this.settings.messages[n.name].remote = o.message, r = "string" == typeof r && {
                    url: r
                } || r, o.old === t ? o.valid : (o.old = t, i = this, this.startRequest(n), s = {}, s[n.name] = t, e.ajax(e.extend(!0, {
                    url: r,
                    mode: "abort",
                    port: "validate" + n.name,
                    dataType: "json",
                    data: s,
                    context: i.currentForm,
                    success: function(r) {
                        var s,
                            u,
                            f,
                            l = r === !0 || "true" === r;
                        i.settings.messages[n.name].remote = o.originalMessage, l ? (f = i.formSubmitted, i.prepareElement(n), i.formSubmitted = f, i.successList.push(n), delete i.invalid[n.name], i.showErrors()) : (s = {}, u = r || i.defaultMessage(n, "remote"), s[n.name] = o.message = e.isFunction(u) ? u(t) : u, i.invalid[n.name] = !0, i.showErrors(s)), o.valid = l, i.stopRequest(n, l)
                    }
                }, r)), "pending")
            }
        }
    }), e.format = function() {
        throw "$.format has been deprecated. Please use $.validator.format instead."
    };
    var t,
        n = {};
    e.ajaxPrefilter ? e.ajaxPrefilter(function(e, t, r) {
        var i = e.port;
        "abort" === e.mode && (n[i] && n[i].abort(), n[i] = r)
    }) : (t = e.ajax, e.ajax = function(r) {
        var i = ("mode" in r ? r : e.ajaxSettings).mode,
            s = ("port" in r ? r : e.ajaxSettings).port;
        return "abort" === i ? (n[s] && n[s].abort(), n[s] = t.apply(this, arguments), n[s]) : t.apply(this, arguments)
    }), e.extend(e.fn, {
        validateDelegate: function(t, n, r) {
            return this.bind(n, function(n) {
                var i = e(n.target);
                return i.is(t) ? r.apply(i, arguments) : void 0
            })
        }
    })
}), define("frontend/Mailchimp", ["jquery", "jquery.form", "jquery.validate"], function(e) {
    var t = function(t) {
        var n = this,
            r,
            s,
            o,
            u,
            a,
            f;
        r = e.extend({
            $e: null,
            selector: ""
        }, t), o = {
            name: "Mailchimp",
            $e: r.$e || e(r.selector),
            mce_validator: [],
            ajaxOptions: {}
        }, u = {
            subscribeForms: o.$e.find(".mc-embedded-subscribe-form"),
            currForm: null,
            succResp: null,
            errorResp: null
        }, a = {
            init: function() {
                if (u.subscribeForms.length == 0)
                    return;
                o.mce_validator = e.map(u.subscribeForms, function(t) {
                    return e(t).validate({
                        errorClass: "mce_inline_error",
                        errorElement: "div",
                        onkeyup: !1,
                        onfocusout: function(t) {
                            a.isTooEarly(t) || e(t).valid()
                        },
                        onblur: function(t) {
                            a.isTooEarly(t) || e(t).valid()
                        },
                        errorPlacement: function(e, t) {
                            t.closest(".mc-field-group").append(e)
                        },
                        submitHandler: function(t) {
                            u.currForm = e(t), e(t).ajaxSubmit(o.ajaxOptions)
                        }
                    })
                }), o.ajaxOptions = {
                    url: a.getAjaxSubmitUrl(),
                    type: "GET",
                    dataType: "json",
                    contentType: "application/json; charset=utf-8",
                    success: a.mce_success_cb
                }
            },
            isTooEarly: function(t) {
                var n = e("input:not(:hidden)", e(t).closest(".mc-field-group"));
                return e(n).eq(-1).attr("id") != e(t).attr("id")
            },
            getAjaxSubmitUrl: function() {
                var t = e("form.mc-embedded-subscribe-form").attr("action");
                return t = t.replace("/post?u=", "/post-json?u=") + "&c=?", t
            },
            mce_success_cb: function(t) {
                u.succResp = u.currForm.find(".mce-success-response"), u.errorResp = u.currForm.find(".mce-error-response"), u.succResp.hide(), u.errorResp.hide();
                if (t.result == "success")
                    u.succResp.show().html("Almost Finished.  Please check your email to confirm your email address."), u.currForm[0].reset(), e.get(e(window.frameElement).attr("click"));
                else {
                    var n = -1,
                        r;
                    try {
                        var s = t.msg.split(" - ", 2);
                        s[1] == undefined ? r = t.msg : (i = parseInt(s[0]), i.toString() == s[0] ? (n = s[0], r = s[1]) : (n = -1, r = t.msg))
                    } catch (a) {
                        n = -1, r = t.msg
                    }
                    try {
                        if (n == -1)
                            u.errorResp.show().html(r);
                        else {
                            var f = e("input[name*='" + fnames[n] + "']").attr("name"),
                                l = {};
                            l[f] = r, o.mce_validator[o.currForm].showErrors(l)
                        }
                    } catch (a) {
                        u.errorResp.show().html(r)
                    }
                }
            }
        }, a.init()
    };
    return t
}), define("frontend/Listings", ["jquery"], function(e) {
    var t = function(t) {
            var n,
                r;
            n = {
                listing_thumbs: e(".thumb[data-image]")
            }, r = {
                init: function() {
                    n.listing_thumbs.each(function(t, n) {
                        var r = e(n).data("image");
                        r && e(n).css("background-image", 'url("' + r + '")')
                    })
                }
            }, r.init()
        },
        n = null;
    return function() {
        return n || (n = new t), n
    }
}), define("frontend/LazyAds", ["jquery", "frontend/globals"], function(e, t) {
    var n = function(n) {
        var r = this,
            i,
            s,
            o,
            u,
            a,
            f;
        i = e.extend({
            show_theshold: 400
        }, n), s = t(), o = {
            win_height: s.elements.window.height(),
            viewport_bottom: s.fn.get_scroll_position() + s.elements.window.height(),
            remaining_ads: null
        }, u = {
            lazy_ads: e("[data-lazy-ad]")
        }, a = {
            init: function() {
                o.remaining_ads = u.lazy_ads, s.elements.document.on("scroll_simple", f.scroll), s.elements.document.on("resize_debounced", f.resize), a.measure_ad_positions(), a.process_ads()
            },
            add_ad: function(e) {
                var t = e.attr("id"),
                    n = targeting_data.lazySlots[t];
                if (!n)
                    return;
                googletag.cmd.push(function() {
                    googletag.pubads().refresh([n])
                }), o.remaining_ads = o.remaining_ads.not(e)
            },
            measure_ad_positions: function() {
                o.remaining_ads.each(function() {
                    var t = e(this);
                    t.data("top_offset", Math.max(t.offset().top, t.parent().offset().top))
                })
            },
            process_ads: function() {
                o.remaining_ads.each(function() {
                    var t = e(this);
                    o.viewport_bottom + i.show_theshold > t.data("top_offset") && a.add_ad(t)
                })
            }
        }, f = {
            scroll: function(e) {
                o.viewport_bottom = e.scroll_top + o.win_height, a.process_ads()
            },
            resize: function(e) {
                o.win_height = e.win_height, o.viewport_bottom = s.fn.get_scroll_position() + e.win_height, a.measure_ad_positions()
            }
        }, a.init()
    };
    return n
}), require.config({
    waitSeconds: 0,
    shim: {
        underscore: {
            exports: "_"
        },
        modernizr: {
            exports: "Modernizr"
        },
        jquery_easing: ["jquery"],
        jquery_mousewheel: ["jquery"],
        jquery_panzoom: ["jquery"],
        "jquery.validate": ["jquery"],
        "jquery.form": ["jquery"],
        "frontend/Article": ["jquery"],
        "frontend/Analytics": ["jquery", "jquery_cookie"],
        "frontend/Mailchimp": ["jquery", "jquery.form", "jquery.validate"],
        "frontend/Sharing": ["jquery"],
        "frontend/Slideshow": ["jquery", "hammer"],
        "frontend/Sidebar": ["jquery"],
        "frontend/Viewer": ["jquery"],
        "frontend/globals": ["jquery", "underscore", "jquery_easing"]
    }
}), require(["jquery", "modernizr", "picturefill", "frontend/globals", "frontend/Header", "frontend/HeaderVerticals", "frontend/Sharing", "frontend/Mailchimp", "frontend/Analytics", "frontend/Listings", "frontend/LazyAds"], function(e, t, n, r, i, s, o, u, a, f, l) {
    r(), i({
        selector: "body"
    }), o({
        selector: "body"
    }), u({
        selector: "body"
    }), l(), a(), f(), e("body").hasClass("js-is-vertical") && s({
        selector: ".js-verticalheader"
    }), document.createElement("picture")
}), define("core", function() {}), define("frontend/TweetThisText", ["jquery", "frontend/globals", "jquery_easing"], function(e, t, n) {
    var r = function() {
            var e,
                t,
                n,
                r,
                i,
                s;
            return window.getSelection ? (e = window.getSelection(), e.rangeCount && (t = e.toString(), n = e.getRangeAt(0).getClientRects()[0], i = n.left, s = n.top)) : document.selection && (e = document.selection, e && e.type != "Control" && (r = e.createRange(), t = r.text, i = r.collapse(!0).boundingLeft, s = r.collapse(!0).boundingTop)), {
                text: t,
                x_pos: i,
                y_pos: s
            }
        },
        i = function(n) {
            var i = this,
                s,
                o,
                u,
                a,
                f,
                l;
            s = e.extend({
                $e: null,
                selector: "",
                text_content_selector: "p, blockquote, .pullquote"
            }, n), o = t(), u = {
                name: "TweetThisText",
                $e: s.$e || e(s.selector),
                hide_popover_timeout: null
            }, a = {
                popover: null,
                text_content: e(s.text_content_selector, u.$e)
            }, f = {
                init: function() {
                    a.text_content.on("mouseup", l.mouseup)
                },
                provide_controls: function() {
                    var t,
                        n,
                        i,
                        s;
                    t = r(), n = t.text, i = t.x_pos, s = t.y_pos, n && n !== "" && i && s && (a.popover || (a.popover = e('<div class="tweet-the-selection-popup" data-share="twitter"><span class="fa fa-twitter"></span></div>'), a.popover.appendTo(e("body"))), a.popover.attr("data-text", n), a.popover.hasClass("visible") ? a.popover.animate({
                        top: o.fn.get_scroll_position() + s - 60,
                        left: i
                    }, 200, "easeInOutQuint") : (a.popover.addClass("notransition").css({
                        top: o.fn.get_scroll_position() + s - 60,
                        left: i
                    }), setTimeout(function() {
                        a.popover.removeClass("notransition")
                    }, 50)), setTimeout(function() {
                        a.popover.addClass("visible")
                    }, 100), clearTimeout(u.hide_popover_timeout), u.hide_popover_timeout = setTimeout(function() {
                        a.popover.removeClass("visible")
                    }, 2e3))
                }
            }, l = {
                mouseup: function(e) {
                    f.provide_controls()
                }
            }, f.init()
        };
    return i
}), define("frontend/FilterSeriesPosts", ["jquery", "frontend/globals"], function(e, t) {
    var n = function(n) {
        var r = this,
            i,
            s,
            o,
            u,
            a,
            f;
        i = e.extend({
            $e: null,
            selector: ""
        }, n), s = t(), o = {
            name: "FilterSeriesPosts",
            $e: i.$e || e(i.selector),
            curr_filter: null
        }, u = {
            tags: o.$e.find(".series-filters .tag"),
            posts: o.$e.find(".series-listings")
        }, a = {
            init: function() {
                u.tags.click(f.switch_filter)
            },
            get_posts: function() {
                e.ajax({
                    url: u.posts.data("series-path"),
                    data: {
                        content_type: o.curr_filter
                    },
                    success: a.display_posts
                })
            },
            display_posts: function(t) {
                t && (t = e(t).attr("data-content-type", o.curr_filter), u.posts.append(t)), u.posts.children().hide().end().children('[data-content-type="' + o.curr_filter + '"]').show()
            },
            update_posts: function() {
                u.posts.find('[data-content-type="' + o.curr_filter + '"]').length ? a.display_posts() : a.get_posts()
            }
        }, f = {
            switch_filter: function() {
                u.tags.removeClass("active"), e(this).addClass("active"), o.curr_filter = e(this).data("tag"), a.update_posts()
            }
        }, a.init()
    };
    return n
});
var Froogaloop = function() {
    function e(t) {
        return new e.fn.init(t)
    }
    function t(e, t, n) {
        if (!n.contentWindow.postMessage)
            return !1;
        e = JSON.stringify({
            method: e,
            value: t
        }), n.contentWindow.postMessage(e, o)
    }
    function n(e) {
        var t,
            n;
        try {
            t = JSON.parse(e.data), n = t.event || t.method
        } catch (r) {}
        "ready" != n || s || (s = !0);
        if (!/^https?:\/\/player.vimeo.com/.test(e.origin))
            return !1;
        "*" === o && (o = e.origin), e = t.value;
        var u = t.data,
            a = "" === a ? null : t.player_id;
        return t = a ? i[a][n] : i[n], n = [], t ? (void 0 !== e && n.push(e), u && n.push(u), a && n.push(a), 0 < n.length ? t.apply(null, n) : t.call()) : !1
    }
    function r(e, t, n) {
        n ? (i[n] || (i[n] = {}), i[n][e] = t) : i[e] = t
    }
    var i = {},
        s = !1,
        o = "*";
    return e.fn = e.prototype = {
        element: null,
        init: function(e) {
            return "string" == typeof e && (e = document.getElementById(e)), this.element = e, this
        },
        api: function(e, n) {
            if (!this.element || !e)
                return !1;
            var i = this.element,
                s = "" !== i.id ? i.id : null,
                o = n && n.constructor && n.call && n.apply ? null : n,
                u = n && n.constructor && n.call && n.apply ? n : null;
            return u && r(e, u, s), t(e, o, i), this
        },
        addEvent: function(e, n) {
            if (!this.element)
                return !1;
            var i = this.element,
                o = "" !== i.id ? i.id : null;
            return r(e, n, o), "ready" != e ? t("addEventListener", e, i) : "ready" == e && s && n.call(null, o), this
        },
        removeEvent: function(e) {
            if (!this.element)
                return !1;
            var n = this.element,
                r = "" !== n.id ? n.id : null;
            e:
            {
                if (r && i[r]) {
                    if (!i[r][e]) {
                        r = !1;
                        break e
                    }
                    i[r][e] = null
                } else {
                    if (!i[e]) {
                        r = !1;
                        break e
                    }
                    i[e] = null
                }
                r = !0
            }"ready" != e && r && t("removeEventListener", e, n)
        }
    }, e.fn.init.prototype = e.fn, window.addEventListener ? window.addEventListener("message", n, !1) : window.attachEvent("onmessage", n), window.Froogaloop = window.$f = e
}();
define("frontend/froogaloop2.min", function() {}), define("frontend/Video", ["jquery", "frontend/Analytics", "frontend/froogaloop2.min"], function(e, t, n) {
    var r = function(n) {
        var r = this,
            i,
            s,
            o,
            u,
            a,
            f;
        i = e.extend({
            $e: null,
            selector: ""
        }, n), s = t(), o = {
            name: "Video",
            $e: i.$e || e(i.selector),
            video_played: !1,
            video_ended: !1,
            ytPlayers: [],
            vPlayers: []
        }, u = {
            hero: o.$e.find(".hero"),
            play_hero_video_button: o.$e.find(".hero .start-video"),
            hero_video_cont: o.$e.find(".hero-video"),
            hero_video_iframe: null,
            video_embeds: {
                youtube: o.$e.find(".js-youtube"),
                vimeo: o.$e.find(".js-vimeo")
            }
        }, a = {
            init: function() {
                var t = document.createElement("script");
                t.src = "https://www.youtube.com/player_api?ver=3.9.2";
                var n = document.getElementsByTagName("script")[0];
                n.parentNode.insertBefore(t, n), window.onYouTubePlayerAPIReady = function() {
                    u.video_embeds.youtube.each(function(t, n) {
                        var r = e(n).data("video-id"),
                            i = {};
                        e(n).data("playlist-id") && (i = {
                            listType: "playlist",
                            list: e(n).data("playlist-id")
                        });
                        var s = new YT.Player(r, {
                            videoId: r,
                            playerVars: e.extend({
                                rel: 0
                            }, i),
                            events: {
                                onStateChange: f.youtube_player_action,
                                onReady: function(e) {}
                            }
                        });
                        o.ytPlayers.push(s)
                    })
                }, u.video_embeds.vimeo.each(function(t, n) {
                    var r = e(n);
                    r.attr("src", r.data("src"));
                    var i = $f(n);
                    i.addEvent("ready", function(e, t, n) {
                        i.addEvent("play", f.vimeo_player_play), i.addEvent("finish", f.vimeo_player_end)
                    }), o.vPlayers.push(i)
                }), u.play_hero_video_button.length > 0 && u.hero.css("cursor", "pointer").click(f.start_hero_video)
            },
            play_hero_video: function() {
                var t = u.hero_video_cont.find("iframe"),
                    n = o.ytPlayers.filter(function(n) {
                        return e(n.c).is(t[0])
                    });
                n.length ? n[0].playVideo() : $f(t[0]).api("play")
            },
            video_player_action: function(t, n) {
                var r = e(n).parents(".hero-video").length ? "Hero" : "Post";
                switch (t) {
                case YT.PlayerState.PLAYING:
                    o.video_played || (o.video_played = !0, s.track("Video Action", {
                        event: "Play",
                        location: r
                    }));
                    break;
                case YT.PlayerState.ENDED:
                    o.video_ended || (o.video_ended = !0, s.track("Video Action", {
                        event: "Finish",
                        location: r
                    }))
                }
            }
        }, f = {
            start_hero_video: function() {
                u.hero_video_cont.height(u.hero.outerHeight()), u.hero.hide(), u.hero_video_cont.show(), a.play_hero_video()
            },
            vimeo_player_play: function(e) {
                a.video_player_action(YT.PlayerState.PLAYING, e)
            },
            vimeo_player_end: function(e) {
                a.video_player_action(YT.PlayerState.ENDED, e)
            },
            youtube_player_action: function(e) {
                a.video_player_action(e.data, e.target.c)
            }
        }, a.init()
    };
    return r
}), define("frontend/LinkManager", ["jquery", "frontend/globals"], function(e, t) {
    var n = function(r) {
        var i = this,
            s,
            o,
            u,
            a,
            f,
            l;
        s = e.extend({
            $e: null,
            selector: ""
        }, r), o = t(), u = {
            name: "LinkManager",
            $e: s.$e || e(s.selector),
            local_link_re: new RegExp("/" + window.location.host + "/"),
            qualified_url_re: new RegExp("^[A-Za-z]{3,7}://")
        }, a = {}, f = {
            init: function() {
                f.manage()
            },
            manage: function() {
                e("a:not(." + n.markup.MANAGED + ")", u.$e).each(function() {
                    f.manage_link(e(this), this.href)
                })
            },
            manage_link: function(e, t) {
                e.addClass(n.markup.MANAGED), t && u.qualified_url_re.test(t) && !u.local_link_re.test(t) && e.addClass(n.markup.EXTERNAL).attr("target", "_blank")
            }
        }, l = {}, f.init()
    };
    return n.markup = {
        MANAGED: "managed-link",
        EXTERNAL: "external-link"
    }, n
}), define("frontend/ParallaxAd", ["jquery", "frontend/globals"], function(e, t) {
    var n = function(n) {
        var r = this,
            i,
            s,
            o,
            u,
            a,
            f,
            l;
        i = e.extend({
            $e: null,
            selector: "",
            min_article_height: 2e3
        }, n), s = t(), o = {
            $e: i.$e || e(i.selector),
            scroll_top: s.fn.get_scroll_position(),
            scroll_direction: "down",
            win_height: s.elements.window.height(),
            ad_width: 0,
            target_height: 0,
            parallaxImg: [],
            parallaxVid: [],
            ratio: 1.7777777
        }, u = {
            article: e("article"),
            ad: o.$e.find(".js-parallax-ad"),
            ad_img: o.$e.find(".js-parallax-ad .img"),
            poster: o.$e.find(".js-vid-poster"),
            article_elements: o.$e.find(".copy > *")
        }, a = {
            init: function() {
                if (u.ad.length === 0)
                    return;
                var e = u.article.height() >= i.min_article_height;
                if (!e)
                    return;
                a.place_ad()
            },
            setup_ad: function() {
                a.set_position();
                var t = /Safari/.test(navigator.userAgent) && /Apple Computer/.test(navigator.vendor);
                s.elements.window.on("resize", f.resize), s.features.can_touch || t || s.elements.document.on("scroll_simple", f.scroll), u.poster.on("click", function() {
                    var t = e(this),
                        n = t.attr("style"),
                        r = e(t.data("embed")).attr("style", n).css({
                            "-webkit-transform": "",
                            "-moz-transform": "",
                            "-ms-transform": "",
                            transform: ""
                        });
                    t.hide().after(r)
                }), window.parallaxPos = u.ad.offset().top
            },
            place_ad: function() {
                var t = u.article_elements.length,
                    n = Math.floor(t / 2) - 1;
                if (u.article_elements.slice(0, n + 1).text().replace(/(\r\n|\n|\r)/gm, "").length < 1e3 || u.article_elements.slice(n + 1).text().replace(/(\r\n|\n|\r)/gm, "").length < 1e3)
                    return !1;
                u.article_elements.slice(n + 1).insertAfter(u.ad), setTimeout(function() {
                    var t = frames["google_ads_iframe_/6709/PostPage/Parallax_0"];
                    if (u.ad_img.css("display") === "block") {
                        try {
                            var n = e(t.document.body);
                            o.parallaxContent = n.find("a")
                        } catch (r) {}
                        o.parallaxContent.length > 0 && (n.css({
                            width: "100%",
                            bottom: 0,
                            display: "block"
                        }), u.ad.show().height(u.ad.width() / o.ratio), o.parallaxContent.css({
                            overflow: "hidden",
                            bottom: 0
                        }), a.setup_ad())
                    }
                }, 1e3)
            },
            set_position: function() {
                o.win_height = s.elements.window.height(), o.ad_width = u.ad.width();
                var e = u.ad,
                    t = u.ad_img,
                    n = e.offset().top;
                s.objects.iscroll && (n += o.scroll_top), e.data("offset_top", n);
                var r = o.ad_width / o.ratio;
                o.win_height > r ? (e.data("target_height", r), e.data("extra_height", o.win_height - r)) : (e.data("target_height", o.win_height), e.data("extra_height", 0)), t.height(e.data("target_height")), o.target_height = e.data("target_height"), a.set_asset_sizes(), s.objects.iscroll && s.objects.iscroll.refresh()
            },
            set_asset_sizes: function() {
                o.parallaxImg.length < 0 && o.parallaxImg.css({
                    width: o.ad_width,
                    height: o.ad_width / o.ratio
                }), u.ad.height(o.ad_width / o.ratio)
            },
            reveal_ad: function() {
                var e = u.ad,
                    t,
                    n,
                    r,
                    i,
                    s = e.data("target_height");
                t = {
                    page_raw: null,
                    page_bounded: null,
                    transform: null,
                    height: null
                }, t.page_raw = function() {
                    return (o.scroll_top + o.win_height - e.data("offset_top")) / o.win_height
                }(), t.page_bounded = function() {
                    return l.keep_inbounds(t.page_raw, 0, 1)
                }(), t.transform = function() {
                    var t = (e.data("offset_top") - o.scroll_top - e.data("extra_height")) / s;
                    return l.keep_inbounds(t, 0, 1)
                }(), t.height = function() {
                    var e = t.transform + t.transform * s / o.win_height;
                    return l.keep_inbounds(e, 0, 1)
                }();
                switch (e.data("transition")) {
                case "reveal":
                    n = s * (1 - t.transform);
                    break;
                case "slide":
                    n = s * (1 - t.height);
                    break;
                case "video":
                    n = s;
                    var a = u.ad_img.data("scrubber");
                    a && (t.video = t.page_raw * .8, t.video <= 0 || t.video >= 1 ? a.stop() : a.seek(t.video));
                    break;
                default:
                    n = s * (1 - t.transform)
                }
                e.css("height", n), i = Math.floor(-1 * t.transform * s), r = "translate3d(0, " + i + "px, 0)", u.ad_img.css({
                    "-webkit-transform": r,
                    "-moz-transform": r,
                    "-ms-transform": r,
                    transform: r
                })
            }
        }, f = {
            scroll: function(e) {
                o.scroll_direction = e.scroll_top >= o.scroll_top ? "down" : "up", o.scroll_top = e.scroll_top, l.is_onscreen(u.ad) && o.ad_width / o.ratio <= o.win_height && a.reveal_ad()
            },
            resize: function() {
                a.set_position()
            }
        }, l = {
            is_onscreen: function(e) {
                var t = o.scroll_top,
                    n = t + o.win_height,
                    r = e.data("offset_top"),
                    i = r + e.data("target_height");
                return r <= n && i >= t
            },
            keep_inbounds: function(e, t, n) {
                return e > n ? e = n : e < t && (e = t), e
            }
        }, a.init()
    };
    return n
}), define("frontend/IncontentAd", ["jquery", "frontend/globals"], function(e, t) {
    var n = function(n) {
        var r = this,
            i,
            s,
            o,
            u,
            a,
            f;
        i = e.extend({
            $e: null,
            selector: "",
            native_ad_index: 1
        }, n), s = t(), o = {
            name: "IncontentAd",
            $e: i.$e || e(i.selector),
            is_vertical: s.elements.body.hasClass("js-is-vertical"),
            disable_ads: e("#disable_ads").length > 0 ? !0 : !1,
            win_height: s.elements.window.height(),
            MAX_ADS: 3,
            INIT_SPACING: 500,
            AD_SPACING: 800,
            AD_SPACING_AFTER: 300,
            SCROLL_BUFFER: 250,
            placements: []
        }, u = {
            article: e("article"),
            article_elements: o.$e.find(".copy > *"),
            sponsor_tags: o.$e.find(".titleblock .tag.sponsor")
        }, a = {
            init: function() {
                if (u.sponsor_tags.length > 0 || typeof googletag == "undefined")
                    return;
                if (s.elements.window.width() > s.properties.phone_max_width)
                    return;
                setTimeout(function() {
                    var t = [];
                    try {
                        var n = frames["google_ads_iframe_/6709/PostPage/Parallax_0"];
                        t = e(n.document.body).find("#google_image_div, #ad_wrapper").find("img")
                    } catch (r) {}
                    t.length === 0 && (a.compute_placements(), a.measure_ad_positions(), s.elements.document.on("scroll_simple", f.scroll), f.scroll({
                        scroll_top: 0
                    }), s.elements.document.on("resize_debounced", f.resize))
                }, 500)
            },
            compute_placements: function() {
                var t = 0,
                    n = a.getLength(u.article_elements),
                    r = n,
                    s = 0,
                    f = Math.max(o.AD_SPACING, n / (o.MAX_ADS + 1));
                for (var l = 0; l < u.article_elements.length - 1; l++) {
                    var c = u.article_elements.eq(l),
                        h = u.article_elements.eq(l + 1),
                        p = a.getLength(c);
                    r -= p, s += p;
                    if (t > o.MAX_ADS - 1)
                        return;
                    if (s < (t === 0 ? o.INIT_SPACING : f) || r < o.AD_SPACING_AFTER)
                        continue;
                    if (!c.is("p") || !h.is("p"))
                        continue;
                    s = 0, googletag.cmd.push(function() {
                        var e = "ad_incontent_" + t,
                            n;
                        o.is_vertical && t == i.native_ad_index ? n = googletag.defineSlot("/6709/PostPage/InContent_2Fluid", ["fluid"], e) : (n = googletag.defineSlot("/6709/PostPage/InContent_" + (t + 1), [300, 250], e), n.defineSizeMapping([[[768, 0], []], [[0, 0], [300, 250]]])), n.addService(googletag.pubads()), targeting_data.lazySlots[e] = n
                    }), e(a.ad_markup(t)).insertAfter(c), o.placements.push({
                        el: c,
                        idx: t
                    }), t++
                }
            },
            ad_id: function(e) {
                return "ad_incontent_" + e
            },
            measure_ad_positions: function() {
                o.placements.length > 0 && e.each(o.placements, function() {
                    var e = this;
                    e.el.data("offset_top", e.el.offset().top), e.el.data("height", e.el.height()), e.el.data("offset_bottom", e.el.data("offset_top") + e.el.data("height"))
                })
            },
            load_ad: function(e) {
                var t = o.placements[0];
                if (e + o.SCROLL_BUFFER > t.el.data("offset_bottom")) {
                    o.placements.shift();
                    var n = targeting_data.lazySlots[a.ad_id(t.idx)];
                    googletag.pubads().refresh([n]), setTimeout(a.measure_ad_positions, 1e3)
                }
            },
            getLength: function(e) {
                return e.text().replace(/(\r\n|\n|\r)/gm, "").length
            },
            ad_markup: function(e) {
                return o.is_vertical && e == i.native_ad_index ? "<div class='image half content-ad " + (e % 2 === 0 ? "left" : "right") + "' id='" + a.ad_id(e) + "'>" + "<script>googletag.cmd.push(function() { googletag.display('" + a.ad_id(e) + "'); });</script>" + "</div>" : "<div class='image half content-ad " + (e % 2 === 0 ? "left" : "right") + "' id='" + a.ad_id(e) + "'>" + "<script>googletag.cmd.push(function() { googletag.display('" + a.ad_id(e) + "'); });</script>" + "</div>"
            }
        }, f = {
            scroll: function(e) {
                o.placements.length > 0 && !o.disable_ads && a.load_ad(e.scroll_top + o.win_height)
            },
            resize: function(e) {
                o.win_height = e.win_height, a.measure_ad_positions()
            }
        }, a.init()
    };
    return n
}), define("frontend/Discussion", ["jquery"], function(e) {
    var t = function(t) {
        var n = this,
            r,
            i,
            s,
            o,
            u,
            a,
            f;
        r = e.extend({
            $e: null,
            selector: "",
            max_avatars_shown: 7
        }, t), o = {
            name: "Discussion",
            $e: r.$e || e(r.selector),
            disqus_id: DISQUS.disqus_identifier,
            disqus_shortname: DISQUS.disqus_shortname
        }, u = {
            avatar_list: o.$e.find(".js-avatars")
        }, a = {
            init: function() {
                a.fetch_avatars()
            },
            fetch_avatars: function() {
                var t = window.location.hostname.indexOf("www.good-qa") === 0 || window.location.hostname.indexOf("local") === 0,
                    n = t ? "oDdTxDPzNUnOHEL11RlS0zeXzlArhyZ5543qpMKf9uxm6EkvdJlSHS3iYk8mTezJ" : "aGG5qmm7m1KtbTRJRjceUqsCdZDi7uQvJOTxUtCx9nR22kcHQpGKdlYe36VBE2sx";
                e.get("https://disqus.com/api/3.0/threads/listPosts.json?api_key=" + n + "&thread:ident=" + o.disqus_id + "&forum=" + o.disqus_shortname, function(t) {
                    var n = t.response.map(function(e) {
                            return e.author.id
                        }),
                        i = t.response.filter(function(e, t) {
                            return n.indexOf(e.author.id) == t
                        }),
                        s = i.length < r.max_avatars_shown ? i.length : r.max_avatars_shown;
                    for (var o = 0; o < s; o++) {
                        var a = i[o].author.avatar.cache,
                            f = e("<li>").append(e("<img>").attr("src", a));
                        u.avatar_list.append(f)
                    }
                    i.length > r.max_avatars_shown && u.avatar_list.append(e('<li class="more">+ ' + (i.length - r.max_avatars_shown) + " others</li>"))
                })
            }
        }, a.init()
    };
    return t
}), define("frontend/OEmbed", ["jquery", "frontend/globals"], function(e, t) {
    var n = function(t) {
        var n = this,
            r,
            i,
            s,
            o,
            u;
        r = e.extend({
            $e: null,
            selector: ""
        }, t), i = {
            name: "OEmbed",
            $e: r.$e || e(r.selector),
            endpoints: {
                twitter: "https://api.twitter.com/1/statuses/oembed.json",
                insta: "https://api.instagram.com/oembed/"
            }
        }, s = {
            twitter_embeds: e(".js-twitter-embed"),
            insta_embeds: e(".js-instagram-embed")
        }, o = {
            init: function() {
                s.twitter_embeds.length && s.twitter_embeds.each(function() {
                    var t = e(this),
                        n = t.data("id");
                    o.add_embed(t, i.endpoints.twitter, {
                        id: n.toString()
                    })
                }), s.insta_embeds.length && s.insta_embeds.each(function() {
                    var t = e(this),
                        n = t.data("id");
                    o.add_embed(t, i.endpoints.insta, {
                        url: "http://instagr.am/p/" + n
                    })
                })
            },
            add_embed: function(t, n, r) {
                e.ajax({
                    type: "GET",
                    dataType: "jsonp",
                    data: r,
                    url: n,
                    success: function(e) {
                        t.html(e.html)
                    }
                })
            }
        }, o.init()
    };
    return n
}), define("frontend/GoodPopup", ["jquery", "frontend/globals", "jquery_easing", "frontend/Analytics"], function(e, t, n, r) {
    var i = function(n) {
        var i = this,
            s,
            o,
            u,
            a,
            f,
            l,
            c;
        s = e.extend({
            $e: null,
            selector: ""
        }, n), o = t(), u = r(), a = {
            name: "Header",
            $e: s.$e || e(s.selector),
            max_prompt_interval: 30,
            cookie_name: "goodpopupfired",
            popup_trigger_pos: 0,
            fired: !1,
            loaded: !1,
            heightCheckTimer: null,
            heightAtLastCheck: null,
            heightCheckTimingInMs: 500,
            heightCheckBodyElem: document.querySelector("body")
        }, f = {
            popup: e(".good-popup"),
            popup_close: e(".good-popup .good-popup-close"),
            popup_trigger: e(".article .copy")
        }, l = {
            init: function() {
                if (e.cookie(a.cookie_name))
                    return;
                a.heightAtLastCheck = a.heightCheckBodyElem.clientHeight, f.popup_trigger.length > 0 && (l.setup_end_of_article_trigger(), l.set_popup_trigger_pos()), a.heightCheckTimer = window.setInterval(l.adjustPopupTrigger, a.heightCheckTimingInMs)
            },
            adjustPopupTrigger: function() {
                a.heightAtLastCheck !== null && a.heightAtLastCheck !== a.heightCheckBodyElem.clientHeight && l.set_popup_trigger_pos()
            },
            set_popup_trigger_pos: function() {
                a.popup_trigger_pos = f.popup_trigger.offset().top + f.popup_trigger.height() - o.elements.window.height()
            },
            setup_end_of_article_trigger: function() {
                o.elements.document.on("scroll_simple", c.scroll), o.elements.document.on("resize_debounced", c.resize), f.popup.click(c.overlay_click), f.popup_close.click(c.close_click)
            },
            activate_fb_like_js: function() {
                (function(e, t, n) {
                    var r,
                        i = e.getElementsByTagName(t)[0];
                    if (e.getElementById(n))
                        return;
                    r = e.createElement(t), r.id = n, r.src = "//connect.facebook.net/en_US/sdk.js#xfbml=1&version=v2.5", i.parentNode.insertBefore(r, i)
                })(document, "script", "facebook-jssdk")
            },
            show_popup: function() {
                if (e.cookie(a.cookie_name))
                    return;
                e.cookie(a.cookie_name, 1, {
                    expires: a.max_prompt_interval,
                    domain: window.location.hostname.substring(window.location.hostname.indexOf("."), window.location.hostname.length)
                }), f.popup.fadeIn(300, function() {
                    f.popup.addClass("state-visible")
                }), u.track("Impression", {
                    placement: "popover",
                    content: "FB Like Box"
                }), o.elements.document.off("scroll_simple", c.scroll), o.elements.document.off("resize_debounced", c.resize), a.heightCheckTimer !== null && (window.clearInterval(a.heightCheckTimer), a.heightCheckTimer = null)
            },
            close_popup: function() {
                f.popup.fadeOut(100, function() {
                    f.popup.removeClass("state-visible")
                })
            }
        }, c = {
            scroll: function(e) {
                !a.loaded && e.scroll_top > a.popup_trigger_pos - 1e3 && (a.loaded = !0, l.activate_fb_like_js()), !a.fired && e.scroll_top > a.popup_trigger_pos && (a.fired = !0, l.show_popup());
                return
            },
            resize: function(e) {
                l.set_popup_trigger_pos()
            },
            overlay_click: function(e) {
                if (e.target != f.popup[0])
                    return;
                l.close_popup()
            },
            close_click: function(e) {
                l.close_popup()
            }
        }, l.init()
    };
    return i
}), define("frontend/Taboola", [], function() {
    var e = function(e) {
        var t = this,
            n = {
                init: function() {
                    window._taboola = window._taboola || [], _taboola.push({
                        article: "auto"
                    }), !function(e, t, n) {
                        e.async = 1, e.src = n, t.parentNode.insertBefore(e, t)
                    }(document.createElement("script"), document.getElementsByTagName("script")[0], "//cdn.taboola.com/libtrc/goodis/loader.js")
                }
            };
        n.init()
    };
    return e
}), define("frontend/InfiniteScroll", ["jquery", "frontend/globals", "frontend/Analytics"], function(e, t, n) {
    var r = function(r) {
        var i = this,
            s,
            o,
            u,
            a,
            f,
            l,
            c;
        s = e.extend({
            $e: null,
            selector: ""
        }, r), o = t(), u = n(), a = {
            name: "InfiniteScroll",
            $e: s.$e || e(s.selector),
            breakpoints: [],
            pageview_count: 1
        }, f = {
            titles: e(".titleblock h1")
        }, l = {
            init: function() {
                if (f.titles.length <= 1)
                    return;
                l.calc_scroll_breakpoints(), o.elements.document.on("scroll_simple", c.scroll)
            },
            calc_scroll_breakpoints: function() {
                f.titles.each(function(e, t) {
                    e > 0 && a.breakpoints.push(t.getBoundingClientRect().top)
                })
            },
            trigger_pageview: function(e) {
                u.track("Pageview", {
                    "infinite scroll depth": e
                })
            }
        }, c = {
            scroll: function(e) {
                e.scroll_top > a.breakpoints[0] - o.elements.window.height() && (a.breakpoints.shift(), l.trigger_pageview(++a.pageview_count))
            }
        }, l.init()
    };
    return r
}), define("frontend/Article", ["jquery", "frontend/globals", "frontend/TweetThisText", "frontend/FilterSeriesPosts", "frontend/Video", "frontend/Analytics", "frontend/LinkManager", "frontend/ParallaxAd", "frontend/IncontentAd", "frontend/Discussion", "frontend/OEmbed", "frontend/GoodPopup", "frontend/Taboola", "frontend/InfiniteScroll"], function(e, t, n, r, i, s, o, u, a, f, l, c, h, p) {
    var d = function(c) {
        var p = this,
            d,
            v,
            m,
            g,
            y,
            b,
            w,
            E;
        d = e.extend({
            $e: null,
            selector: "",
            allow_parallax_hero: !0,
            parallax_rate: .65,
            progressbar_transition_speed: 200,
            show_progressbar: !0
        }, c), v = t(), m = s(), g = h(), y = {
            name: "Article",
            $e: d.$e || e(d.selector),
            color_palette: {
                primary: null,
                secondary: null,
                header_flavor: null
            },
            parallax_hero: null,
            using_parallax_hero: !1,
            scrolled_to_half: !1,
            contentType: null,
            copy_breakpoint: null,
            om_fired: !1,
            core_article_height: 0,
            scroll_top: v.fn.get_scroll_position(),
            win_height: v.elements.window.height(),
            progressbar_is_animating: !1
        }, b = {
            hero: y.$e.find(".hero"),
            titleblock: y.$e.find(".titleblock"),
            sections: y.$e.find("> section"),
            core_article: y.$e.find("section.first"),
            more_link: y.$e.find(".more-link"),
            hidden_copy: y.$e.find(".copy.hidden"),
            sidecol: y.$e.find(".js-sidecol"),
            copy: y.$e.find(".copy"),
            progressbar: e(".js-progressbar"),
            author_module: y.$e.find(".author-module")
        }, w = {
            init: function() {
                w.init_color_palette(), w.init_social_counts(), w.init_tracking_pixel(), w.measure_article_height(), v.fn.setup_hanging_punctuation(y.$e.find("p, h1, h2")), d.allow_parallax_hero && w.init_parallax_hero(), y.contentType = window.location.pathname.split("/")[1], b.copy.length > 0 ? y.copy_breakpoint = b.copy.offset().top + b.copy.height() / 2 : y.copy_breakpoint = null, v.elements.document.on("resize_debounced", E.resize), v.elements.document.on("scroll_simple", E.scroll), new n({
                    $e: y.$e
                }), new r({
                    $e: y.$e
                }), new i({
                    $e: y.$e
                }), new o({
                    $e: y.$e
                }), new u({
                    $e: y.$e
                }), new l, new a({
                    $e: y.$e
                }), y.$e.hasClass("js-discussion") && (y.discussion = new f({
                    $e: y.$e
                })), b.more_link.click(E.show_more_copy), b.author_module.click(E.author_module_click), w.legacy_setup_images(), w.legacy_setup_embeds(), w.legacy_clean_text()
            },
            init_color_palette: function() {
                var t = y.color_palette;
                t.primary = y.$e.data("primarycolor"), t.secondary = y.$e.data("secondarycolor"), t.bgcolor = y.$e.data("bgcolor");
                if (!t.primary || t.primary == "default")
                    t.primary = v.properties.accent_color;
                if (!t.secondary || t.secondary == "default")
                    t.secondary = v.properties.accent_color;
                if (!t.bgcolor || t.bgcolor == "default")
                    t.bgcolor = "#ffffff";
                t.primary_rgb = v.helpers.hex_to_rgb(t.primary), t.primary_rgb_string = "rgb(" + t.primary_rgb[0] + "," + t.primary_rgb[1] + "," + t.primary_rgb[2] + ")", t.bgcolor_rgb = v.helpers.hex_to_rgb(t.bgcolor), t.bgcolor_rgb_string = "rgb(" + t.bgcolor_rgb[0] + "," + t.bgcolor_rgb[1] + "," + t.bgcolor_rgb[2] + ")", e(".article .primarycolor-color").css("color", t.primary), e(".article p a").css("color", t.primary).css("text-shadow", ".03em 0 " + t.bgcolor + ", -.03em 0 " + t.bgcolor + ", 0 .03em " + t.bgcolor + ", 0 -.03em " + t.bgcolor + ", .06em 0 " + t.bgcolor + ", -.06em 0 " + t.bgcolor + ", .09em 0 " + t.bgcolor + ", -.09em 0 " + t.bgcolor + ", .12em 0 " + t.bgcolor + ", -.12em 0 " + t.bgcolor + ", .15em 0 " + t.bgcolor + ", -.15em 0 " + t.bgcolor).css("background-image", "-webkit-linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), -webkit-linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), -webkit-linear-gradient(" + t.primary_rgb_string + ", " + t.primary_rgb_string + ")").css("background-image", "-moz-linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), -moz-linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), -moz-linear-gradient(" + t.primary_rgb_string + ", " + t.primary_rgb_string + ")").css("background-image", "-o-linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), -o-linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), -o-linear-gradient(" + t.primary_rgb_string + ", " + t.primary_rgb_string + ")").css("background-image", "-ms-linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), -ms-linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), -ms-linear-gradient(" + t.primary_rgb_string + ", " + t.primary_rgb_string + ")").css("background-image", "linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), linear-gradient(" + t.bgcolor_rgb_string + ", " + t.bgcolor_rgb_string + "), linear-gradient(" + t.primary_rgb_string + ", " + t.primary_rgb_string + ")"), e(".article .primarycolor-bg").css("background-color", t.primary), e(".article .primarycolor-bordercolor").css("border-color", t.primary), e(".article .secondarycolor-color").css("color", t.secondary), v.elements.pulltab_bg.css("fill", t.secondary)
            },
            init_social_counts: function() {
                var t,
                    n;
                n = location.host + location.pathname, t = {
                    facebook: y.$e.find(".js-facebook-count")
                };
                var r = function(e, n) {
                    var r = parseInt(t[e].text());
                    n && (r ? t[e].text(r + n) : t[e].text(n))
                };
                if (t.facebook.length) {
                    var i = "https://" + n;
                    e.getJSON("//graph.facebook.com/?ids=" + i, function(e) {
                        if (e[i] && e[i].share) {
                            var t = e[i].share.share_count;
                            t >= 100 && r("facebook", t)
                        }
                    })
                }
            },
            init_parallax_hero: function() {
                !v.features.can_touch && b.hero.length > 0 && (y.parallax_hero = b.hero.filter(":visible"), y.parallax_hero.addClass("parallax").css({
                    "will-change": "transform",
                    "-webkit-backface-visibility": "hidden",
                    "backface-visibility": "hidden"
                }).data("bottom_pos", b.hero.offset().top + b.hero.outerHeight()).wrap('<div class="parallax-hero-container" style="overflow: hidden; -webkit-backface-visibility: hidden; backface-visibility: hidden; will-change: contents"></div>'), y.using_parallax_hero = !0)
            },
            init_tracking_pixel: function() {
                var t = e("img[data-pixel-src]");
                if (t.length) {
                    var n = decodeURIComponent(t.data("pixel-src")).replace("timestamp", (new Date).valueOf());
                    t.after(e("<img>").attr("src", n).hide()), t.remove()
                }
            },
            measure_article_height: function() {
                y.core_article_height = b.core_article.outerHeight() - y.win_height
            },
            legacy_setup_images: function() {
                var t = y.$e.find(".js-legacy-content img");
                t.each(function(t) {
                    var n,
                        r,
                        i,
                        s,
                        o;
                    n = e(this), i = n.parent();
                    if (!n.attr("src"))
                        return;
                    i.is("a") && (o = i.attr("href"), s = i, i = i.parent()), r = "" + (o ? '<a href="' + o + '">' : "") + '<div class="image ' + (t === 0 ? "offset" : "standard") + '">' + '<div class="imgarea"><img src="' + n.attr("src") + '" alt="" /></div>' + "</div>" + (o ? "</a>" : ""), i.is("p") || i.is('div:not(".js-legacy-content")') ? (e(r).insertBefore(i), n.remove(), i.text() === "" && i.remove()) : (e(r).insertBefore(n), n.remove()), s && s.remove()
                })
            },
            legacy_setup_embeds: function() {
                var t = y.$e.find(".js-legacy-content .embed-container");
                t.each(function(t) {
                    var n,
                        r;
                    n = e(this), r = '<div class="video left_offset"><div class="membrane">' + n.html() + "</div>" + "</div>", e(r).insertBefore(n), n.remove()
                })
            },
            legacy_clean_text: function() {
                var t = y.$e.find(".js-legacy-content").find("p, div");
                t.each(function(t) {
                    var n = e(this);
                    n.css({
                        "font-family": "",
                        "font-size": "",
                        font: "",
                        "background-color": "",
                        color: ""
                    }), !n.text().trim() && n.children(":not(br)").length < 1 && n.remove()
                })
            }
        }, E = {
            resize: function(e) {
                y.win_height = e.win_height, y.using_parallax_hero && b.hero.length > 0 && b.hero.data("bottom_pos", b.hero.offset().top + b.hero.outerHeight()), w.measure_article_height()
            },
            scroll: function(e) {
                y.scroll_top = e.scroll_top, !y.scrolled_to_half && y.contentType != "videos" && y.contentType != "slideshows" && y.scroll_top > y.copy_breakpoint && (y.scrolled_to_half = !0);
                if (y.using_parallax_hero && y.scroll_top * d.parallax_rate < d.parallax_rate * y.parallax_hero.data("bottom_pos")) {
                    var t = Math.floor(y.scroll_top * d.parallax_rate),
                        n = "translate3d(0," + t + "px, 0)";
                    y.parallax_hero.css({
                        "-webkit-transform": n,
                        "-moz-transform": n,
                        "-ms-transform": n,
                        transform: n
                    })
                }
                if (d.show_progressbar && !y.progressbar_is_animating) {
                    var r = y.scroll_top / y.core_article_height;
                    r <= 1 && r >= 0 && (b.progressbar.width(r * 101 + "vw"), y.progressbar_is_animating = !0, setTimeout(function() {
                        y.progressbar_is_animating = !1
                    }, d.progressbar_transition_speed))
                }
            },
            show_more_copy: function() {
                b.more_link.hide(), b.hidden_copy.show()
            },
            author_module_click: function(e) {
                var t,
                    n = e.target.className;
                n.indexOf("headshot") !== -1 ? t = "photo" : n === "author-name" ? t = "name" : n === "managed-link" ? t = "post title" : n.indexOf("more-by-author") !== -1 && n.indexOf("managed-link") !== -1 ? t = "more posts" : n === "more-author-info" && (t = "more info"), t && m.track("Author Module Click", {
                    target: t
                })
            }
        }, w.init()
    };
    return d
}), define("frontend/NewSidebar", ["jquery", "frontend/globals", "frontend/Analytics"], function(e, t, n) {
    var r = function(r) {
        var i = this,
            s,
            o,
            u,
            a,
            f,
            l,
            c;
        s = e.extend({
            $e: null,
            selector: "",
            sidebar_matches_height_of: e("article section.first"),
            sticky_dist: 500
        }, r), o = t(), u = n(), a = {
            name: "NewSidebar",
            $e: s.$e || e(s.selector),
            scroll_top: o.fn.get_scroll_position(),
            win_width: o.elements.window.width(),
            win_height: o.elements.window.height(),
            sidebar_offset_top: null,
            sidebar_offset_bottom: null,
            sidebar_height: null,
            maincontent_offset_top: null,
            maincontent_offset_bottom: null,
            maincontent_height: null,
            maincontent_usuable_height: null,
            sidebar_height_factor: null,
            sidebar_state: "none",
            loaded: {
                related: !1,
                mostread: !1
            },
            postID: null
        }, f = {
            article: e("article section.first"),
            admin_link: e(".admin-edit a"),
            rankings_nav_items: a.$e.find(".js-rankings-nav [data-target]"),
            rankings: a.$e.find(".js-rankings-holder"),
            rankings_placeholder: a.$e.find(".js-rankings-placeholder"),
            rankings_lists: a.$e.find(".js-rankings"),
            rankings_items: a.$e.find(".js-mixpanel-ranking-item"),
            below_rankings: a.$e.find(".js-below-rankings-content"),
            above_rankings: a.$e.find(".js-above-rankings"),
            first_child: a.$e.children().eq(0)
        }, l = {
            init: function() {
                a.$e.length > 0 && (a.postID = f.admin_link.attr("href").match(/[\d]+/), l.load_and_insert_list("related"), l.load_and_insert_list("mostread"), setTimeout(l.measure_and_set_sidebar_positions, 1), setTimeout(l.measure_and_set_sidebar_positions, 2e3), setTimeout(l.measure_and_set_sidebar_positions, 4e3), f.rankings_nav_items.on("click", c.rankings_nav_click), o.elements.document.on("scroll_simple", c.scroll), o.elements.document.on("resize_debounced", c.resize), o.elements.document.on("disqus_updated", c.disqus_updated), f.rankings_items.on("click", c.track_rankings_item_click))
            },
            measure_and_set_sidebar_positions: function() {
                a.sidebar_state = "none", a.$e.removeClass("state-fixed state-absolute").css({
                    "min-height": a.win_height - parseInt(a.$e.css("padding-top").replace("px", ""), 10),
                    top: "",
                    "-webkit-transform": "",
                    "-moz-transform": "",
                    "-ms-transform": "",
                    transform: ""
                }), a.sidebar_offset_top = a.$e.offset().top, a.sidebar_height = a.$e.outerHeight(), a.sidebar_offset_bottom = a.sidebar_offset_top + a.sidebar_height, a.$e.addClass("state-absolute").css({
                    top: a.sidebar_offset_top
                }), a.sidebar_state = "absolute", a.maincontent_offset_top = s.sidebar_matches_height_of.offset().top, a.maincontent_height = s.sidebar_matches_height_of.outerHeight(), a.maincontent_offset_bottom = a.maincontent_offset_top + a.maincontent_height, a.maincontent_usuable_height = a.maincontent_height - (a.sidebar_offset_top - a.maincontent_offset_top) - parseInt(s.sidebar_matches_height_of.css("padding-top").replace("px", ""), 10) - parseInt(s.sidebar_matches_height_of.css("padding-bottom").replace("px", ""), 10), a.sidebar_height_factor = (a.sidebar_height - a.win_height + s.sticky_dist) / (a.maincontent_usuable_height - a.win_height), l.set_sidebar_offset_with_fixed_positioning()
            },
            set_sidebar_offset: function() {
                var e,
                    t;
                if (a.scroll_top >= a.sidebar_offset_top) {
                    a.scroll_top <= a.maincontent_offset_bottom - a.win_height ? t = a.scroll_top - a.sidebar_offset_top : t = a.maincontent_offset_bottom - a.win_height - a.sidebar_offset_top;
                    var n = t - t * a.sidebar_height_factor;
                    o.features.can_translate3d ? e = "translate3d(0," + n + "px, 0)" : e = "translate(0," + n + "px)"
                } else
                    a.scroll_top < a.sidebar_offset_top ? e = "none" : e = null;
                e && a.$e.css({
                    "-webkit-transform": e,
                    "-moz-transform": e,
                    "-ms-transform": e,
                    transform: e
                })
            },
            set_sidebar_offset_with_fixed_positioning: function() {
                var e,
                    t,
                    n,
                    r,
                    i;
                a.scroll_top > a.maincontent_offset_bottom - a.win_height ? (i = a.maincontent_offset_bottom - a.win_height - a.sidebar_offset_top, t = i - i * a.sidebar_height_factor + s.sticky_dist, o.features.can_translate3d ? e = "translate3d(0," + t + "px, 0)" : e = "translate(0," + t + "px)", a.sidebar_state != "absolute" && (r = !0, a.sidebar_state = "absolute")) : a.scroll_top >= a.sidebar_offset_top ? (i = a.scroll_top - a.sidebar_offset_top, t = -1 * i * a.sidebar_height_factor + s.sticky_dist, t > 0 && (t = 0), o.features.can_translate3d ? e = "translate3d(0," + t + "px, 0)" : e = "translate(0," + t + "px)", a.sidebar_state != "fixed" && (n = !0, a.sidebar_state = "fixed")) : a.scroll_top < a.sidebar_offset_top ? (e = "none", a.sidebar_state != "absolute" && (r = !0, a.sidebar_state = "absolute")) : e = null, e && (n && a.$e.removeClass("state-absolute").addClass("state-fixed").css({
                    top: ""
                }), r && a.$e.removeClass("state-fixed").addClass("state-absolute").css({
                    top: a.sidebar_offset_top
                }), a.$e.css({
                    "-webkit-transform": e,
                    "-moz-transform": e,
                    "-ms-transform": e,
                    transform: e
                }))
            },
            load_and_insert_list: function(t) {
                e.ajax({
                    url: "/posts/" + a.postID + "/mixpanel/" + t,
                    success: function(e) {
                        a.loaded[t] = !0, f.rankings_lists.filter(".js-" + t).replaceWith(e), l.set_sidebar_offset_with_fixed_positioning()
                    }
                })
            }
        }, c = {
            resize: function(e) {
                a.win_width = e.win_width, a.win_height = e.win_height, l.measure_and_set_sidebar_positions()
            },
            scroll: function(e) {
                a.win_width > o.properties.phone_max_width && (a.scroll_top = e.scroll_top, l.set_sidebar_offset_with_fixed_positioning())
            },
            rankings_nav_click: function(t) {
                a.$e.find(e(this).data("target")).show().siblings(".js-rankings").hide(), e(this).addClass("state-current").siblings().removeClass("state-current"), l.measure_and_set_sidebar_positions()
            },
            track_rankings_item_click: function() {
                u.track("Sidebar Ranking Item Clicked")
            },
            disqus_updated: function() {
                console.log("disqus updated"), setTimeout(l.set_sidebar_offset_with_fixed_positioning, 500)
            }
        }, l.init()
    };
    return r
}), define("frontend/StickyAd", ["jquery", "frontend/globals"], function(e, t) {
    var n = function(n) {
        var r = this,
            i,
            s,
            o,
            u,
            a,
            f;
        i = e.extend({
            $e: null,
            selector: "",
            ad_top_padding: 72,
            sticky_dist: 500
        }, n), s = t(), o = {
            name: "StickyAd",
            $e: i.$e || e(i.selector),
            scroll_top: s.fn.get_scroll_position(),
            win_width: s.elements.window.width(),
            win_height: s.elements.window.height(),
            sidecol_offset_top: null,
            sidecol_offset_bottom: null,
            sidecol_height: null,
            sidecol_offset_left: null,
            sidecol_padding_left: null,
            sidecol_width: null,
            sidecol_offset_right: null,
            ad_height: 0,
            ad_state: null
        }, u = {
            sidecol: o.$e.find(".js-sidecol"),
            ad: o.$e.find(".js-sidecol .ad").first(),
            placeholder_ad: null,
            hero: o.$e.find(".parallax-hero-container, .hero").first(),
            titleblock: o.$e.find(".titleblock")
        }, a = {
            init: function() {
                u.sidecol.length > 0 && u.ad.length > 0 && o.win_width > s.properties.tablet_max_width && (a.move_sidecol_up(), u.sidecol.css({
                    "margin-bottom": i.sticky_dist,
                    "padding-top": i.ad_top_padding
                }), u.placeholder_ad = e('<div class="placeholder-ad"></div>'), u.sidecol.append(u.placeholder_ad), a.reset_ad_position(), setTimeout(a.measure_and_set_sidecol_positions, 1), setTimeout(a.measure_and_set_sidecol_positions, 2e3), setTimeout(a.measure_and_set_sidecol_positions, 4e3), s.elements.document.on("scroll_simple", f.scroll), s.elements.document.on("resize_debounced", f.resize))
            },
            move_sidecol_up: function() {
                u.sidecol.css("margin-top", "0");
                if (s.elements.window.width() > s.properties.tablet_max_width) {
                    var e;
                    u.hero.length > 0 ? e = u.sidecol.offset().top - (u.hero.offset().top + u.hero.outerHeight()) - 54 : e = u.titleblock.outerHeight() + parseInt(u.titleblock.css("margin-bottom").replace("px", ""), 10) - 12, u.sidecol.css("margin-top", -1 * e)
                }
            },
            reset_ad_position: function() {
                u.ad.css({
                    position: "absolute",
                    top: "0",
                    left: "0"
                }), o.ad_state = "reset"
            },
            measure_and_set_sidecol_positions: function() {
                a.reset_ad_position(), o.ad_height = u.ad.outerHeight(), u.placeholder_ad.css({
                    height: o.ad_height
                }), o.sidecol_offset_top = u.sidecol.offset().top, o.sidecol_height = u.sidecol.outerHeight(), o.sidecol_offset_bottom = o.sidecol_offset_top + o.sidecol_height, o.sidecol_offset_left = u.sidecol.offset().left, o.sidecol_width = u.sidecol.outerWidth(), o.sidecol_offset_right = o.sidecol_offset_left + o.sidecol_width, o.sidecol_padding_left = u.sidecol.css("padding-left") ? parseInt(u.sidecol.css("padding-left").replace("px", "")) : 0, a.set_ad_state()
            },
            set_ad_state: function() {
                var e = o.scroll_top - o.sidecol_offset_top;
                e < -1 * i.ad_top_padding ? o.ad_state != "absolute top" && (u.ad.css({
                    position: "absolute",
                    top: "0",
                    left: o.sidecol_padding_left
                }), o.ad_state = "absolute top") : e <= i.sticky_dist ? o.ad_state != "fixed" && (u.ad.css({
                    position: "fixed",
                    top: i.ad_top_padding,
                    left: o.sidecol_offset_left + o.sidecol_padding_left
                }), o.ad_state = "fixed") : e > i.sticky_dist && o.ad_state != "absolute bottom" && (u.ad.css({
                    position: "absolute",
                    top: i.sticky_dist + i.ad_top_padding,
                    left: o.sidecol_padding_left
                }), o.ad_state = "absolute bottom")
            }
        }, f = {
            resize: function(e) {
                o.win_width = e.win_width, o.win_height = e.win_height, a.move_sidecol_up(), a.measure_and_set_sidecol_positions()
            },
            scroll: function(e) {
                o.scroll_top = e.scroll_top, a.set_ad_state()
            }
        }, a.init()
    };
    return n
}), require(["jquery", "core", "frontend/Article", "frontend/NewSidebar", "frontend/StickyAd"], function(e, t, n, r, i) {
    var s = new n({
            selector: "article.article"
        }),
        o = new r({
            selector: ".js-sidebar"
        })
}), define("article_main", function() {});


if (!window.__twttrlr) {
    (function(e, t) {
        function y(e) {
            for (var t = 1, n; n = arguments[t]; t++)
                for (var r in n)
                    e[r] = n[r];
            return e
        }
        function b(e) {
            return Array.prototype.slice.call(e)
        }
        function E(e, t) {
            for (var n = 0, r; r = e[n]; n++)
                if (t == r)
                    return n;
            return -1
        }
        function S() {
            var e = b(arguments),
                t = [];
            for (var n = 0, r = e.length; n < r; n++)
                e[n].length > 0 && t.push(e[n].replace(/\/$/, ""));
            return t.join("/")
        }
        function x(e, t, n) {
            var r = t.split("/"),
                i = e;
            while (r.length > 1) {
                var s = r.shift();
                i = i[s] = i[s] || {}
            }
            i[r[0]] = n
        }
        function T() {}
        function N(e, t) {
            this.id = this.path = e, this.force = !!t
        }
        function C(e, t) {
            this.id = e, this.body = t, typeof t == "undefined" && (this.path = this.resolvePath(e))
        }
        function k(e, t) {
            this.deps = e, this.collectResults = t, this.deps.length == 0 && this.complete()
        }
        function L(e, t) {
            this.deps = e, this.collectResults = t
        }
        function A() {
            for (var e in r)
                if (r[e].readyState == "interactive")
                    return c[r[e].id]
        }
        function O(e, t) {
            var r;
            return !e && n && (r = l || A()), r ? (delete c[r.scriptId], r.body = t, r.execute()) : (f = r = new C(e, t), a[r.id] = r), r
        }
        function M() {
            var e = b(arguments),
                t,
                n;
            return typeof e[0] == "string" && (t = e.shift()), n = e.shift(), O(t, n)
        }
        function _(e, t) {
            var n = t.id || "",
                r = n.split("/");
            r.pop();
            var i = r.join("/");
            return e.replace(/^\./, i)
        }
        function D(e, t) {
            function r(e) {
                return C.exports[_(e, t)]
            }
            var n = [];
            for (var i = 0, s = e.length; i < s; i++) {
                if (e[i] == "require") {
                    n.push(r);
                    continue
                }
                if (e[i] == "exports") {
                    t.exports = t.exports || {}, n.push(t.exports);
                    continue
                }
                n.push(r(e[i]))
            }
            return n
        }
        function P() {
            var e = b(arguments),
                t = [],
                n,
                r;
            return typeof e[0] == "string" && (n = e.shift()), w(e[0]) && (t = e.shift()), r = e.shift(), O(n, function(e) {
                function s() {
                    var i = D(b(t), n),
                        s;
                    typeof r == "function" ? s = r.apply(n, i) : s = r, typeof s == "undefined" && (s = n.exports), e(s)
                }
                var n = this,
                    i = [];
                for (var o = 0, u = t.length; o < u; o++) {
                    var a = t[o];
                    E(["require", "exports"], a) == -1 && i.push(_(a, n))
                }
                i.length > 0 ? H.apply(this, i.concat(s)) : s()
            })
        }
        function H() {
            var e = b(arguments),
                t,
                n;
            typeof e[e.length - 1] == "function" && (t = e.pop()), typeof e[e.length - 1] == "boolean" && (n = e.pop());
            var r = new k(B(e, n), n);
            return t && r.then(t), r
        }
        function B(e, t) {
            var n = [];
            for (var r = 0, i; i = e[r]; r++)
                typeof i == "string" && (i = j(i)), w(i) && (i = new L(B(i, t), t)), n.push(i);
            return n
        }
        function j(e) {
            var t,
                n;
            for (var r = 0, i; i = H.matchers[r]; r++) {
                var s = i[0],
                    o = i[1];
                if (t = e.match(s))
                    return o(e)
            }
            throw new Error(e + " was not recognised by loader")
        }
        function I() {
            return e.using = h, e.provide = p, e.define = d, e.loadrunner = v, F
        }
        function q(e) {
            for (var t = 0; t < H.bundles.length; t++)
                for (var n in H.bundles[t])
                    if (n != e && E(H.bundles[t][n], e) > -1)
                        return n
        }
        var n = e.attachEvent && !e.opera,
            r = t.getElementsByTagName("script"),
            i = 0,
            s,
            o = t.createElement("script"),
            u = {},
            a = {},
            f,
            l,
            c = {},
            h = e.using,
            p = e.provide,
            d = e.define,
            v = e.loadrunner;
        for (var m = 0, g; g = r[m]; m++)
            if (g.src.match(/loadrunner\.js(\?|#|$)/)) {
                s = g;
                break
            }
        var w = Array.isArray || function(e) {
            return e.constructor == Array
        };
        T.prototype.then = function(t) {
            var n = this;
            return this.started || (this.started = !0, this.start()), this.completed ? t.apply(e, this.results) : (this.callbacks = this.callbacks || [], this.callbacks.push(t)), this
        }, T.prototype.start = function() {}, T.prototype.complete = function() {
            if (!this.completed) {
                this.results = b(arguments), this.completed = !0;
                if (this.callbacks)
                    for (var t = 0, n; n = this.callbacks[t]; t++)
                        n.apply(e, this.results)
            }
        }, N.loaded = [], N.prototype = new T, N.prototype.start = function() {
            var e = this,
                t,
                n,
                r;
            return (r = a[this.id]) ? (r.then(function() {
                e.complete()
            }), this) : ((t = u[this.id]) ? t.then(function() {
                e.loaded()
            }) : !this.force && E(N.loaded, this.id) > -1 ? this.loaded() : (n = q(this.id)) ? H(n, function() {
                e.loaded()
            }) : this.load(), this)
        }, N.prototype.load = function() {
            var t = this;
            u[this.id] = t;
            var n = o.cloneNode(!1);
            this.scriptId = n.id = "LR" + ++i, n.type = "text/javascript", n.async = !0, n.onerror = function() {
                throw new Error(t.path + " not loaded")
            }, n.onreadystatechange = n.onload = function(n) {
                n = e.event || n;
                if (n.type == "load" || E(["loaded", "complete"], this.readyState) > -1)
                    this.onreadystatechange = null, t.loaded()
            }, n.src = this.path, l = this, r[0].parentNode.insertBefore(n, r[0]), l = null, c[n.id] = this
        }, N.prototype.loaded = function() {
            this.complete()
        }, N.prototype.complete = function() {
            E(N.loaded, this.id) == -1 && N.loaded.push(this.id), delete u[this.id], T.prototype.complete.apply(this, arguments)
        }, C.exports = {}, C.prototype = new N, C.prototype.resolvePath = function(e) {
            return S(H.path, e + ".js")
        }, C.prototype.start = function() {
            var e,
                t,
                n = this,
                r;
            this.body ? this.execute() : (e = C.exports[this.id]) ? this.exp(e) : (t = a[this.id]) ? t.then(function(e) {
                n.exp(e)
            }) : (bundle = q(this.id)) ? H(bundle, function() {
                n.start()
            }) : (a[this.id] = this, this.load())
        }, C.prototype.loaded = function() {
            var e,
                t,
                r = this;
            n ? (t = C.exports[this.id]) ? this.exp(t) : (e = a[this.id]) && e.then(function(e) {
                r.exp(e)
            }) : (e = f, f = null, e.id = e.id || this.id, e.then(function(e) {
                r.exp(e)
            }))
        }, C.prototype.complete = function() {
            delete a[this.id], N.prototype.complete.apply(this, arguments)
        }, C.prototype.execute = function() {
            var e = this;
            typeof this.body == "object" ? this.exp(this.body) : typeof this.body == "function" && this.body.apply(window, [function(t) {
                e.exp(t)
            }])
        }, C.prototype.exp = function(e) {
            this.complete(this.exports = C.exports[this.id] = e || {})
        }, k.prototype = new T, k.prototype.start = function() {
            function t() {
                var t = [];
                e.collectResults && (t[0] = {});
                for (var n = 0, r; r = e.deps[n]; n++) {
                    if (!r.completed)
                        return;
                    r.results.length > 0 && (e.collectResults ? r instanceof L ? y(t[0], r.results[0]) : x(t[0], r.id, r.results[0]) : t = t.concat(r.results))
                }
                e.complete.apply(e, t)
            }
            var e = this;
            for (var n = 0, r; r = this.deps[n]; n++)
                r.then(t);
            return this
        }, L.prototype = new T, L.prototype.start = function() {
            var e = this,
                t = 0,
                n = [];
            return e.collectResults && (n[0] = {}), function r() {
                var i = e.deps[t++];
                i ? i.then(function(t) {
                    i.results.length > 0 && (e.collectResults ? i instanceof L ? y(n[0], i.results[0]) : x(n[0], i.id, i.results[0]) : n.push(i.results[0])), r()
                }) : e.complete.apply(e, n)
            }(), this
        }, P.amd = {};
        var F = function(e) {
            return e(H, M, F, define)
        };
        F.Script = N, F.Module = C, F.Collection = k, F.Sequence = L, F.Dependency = T, F.noConflict = I, e.loadrunner = F, e.using = H, e.provide = M, e.define = P, H.path = "", H.matchers = [], H.matchers.add = function(e, t) {
            this.unshift([e, t])
        }, H.matchers.add(/(^script!|\.js$)/, function(e) {
            var t = new N(e.replace(/^\$/, H.path.replace(/\/$/, "") + "/").replace(/^script!/, ""), !1);
            return t.id = e, t
        }), H.matchers.add(/^[a-zA-Z0-9_\-\/]+$/, function(e) {
            return new C(e)
        }), H.bundles = [], s && (H.path = window.__twttrLoadRunnerPath || s.getAttribute("data-path") || s.src.split(/loadrunner\.js/)[0] || "", (main = s.getAttribute("data-main")) && H.apply(e, main.split(/\s*,\s*/)).then(function() {}))
    })(this, document);
    (window.__twttrlr = loadrunner.noConflict());
}
__twttrlr(function(using, provide, loadrunner, define) {
    provide("util/util", function(e) {
        function t(e) {
            return e && String(e).toLowerCase().indexOf("[native code]") > -1
        }
        function n(e) {
            return o(arguments, function(t) {
                s(t, function(t, n) {
                    e[t] = n
                })
            }), e
        }
        function r(e) {
            return s(e, function(t, n) {
                v(n) && (r(n), m(n) && delete e[t]), (n === undefined || n === null || n === "") && delete e[t]
            }), e
        }
        function s(e, t) {
            for (var n in e)
                (!e.hasOwnProperty || e.hasOwnProperty(n)) && t(n, e[n]);
            return e
        }
        function c(e) {
            return {}.toString.call(e).match(/\s([a-zA-Z]+)/)[1].toLowerCase()
        }
        function h(e, t) {
            return e == c(t)
        }
        function p(e, t, n) {
            return n = n || [], function() {
                var r = a(arguments, function(e) {
                    return e
                });
                return e.apply(t, n.concat(r))
            }
        }
        function v(e) {
            return e === Object(e)
        }
        function m(e) {
            if (!v(e))
                return !1;
            if (Object.keys)
                return !Object.keys(e).length;
            for (var t in e)
                if (e.hasOwnProperty(t))
                    return !1;
            return !0
        }
        function g(e, t) {
            window.setTimeout(function() {
                e.call(t || null)
            }, 0)
        }
        var i = function() {
                var e = Array.prototype.indexOf;
                return t(e) ? function(t, n) {
                    return t ? e.apply(t, [n]) : -1
                } : function(e, t) {
                    if (!e)
                        return -1;
                    for (var n = 0, r = e.length; n < r; n++)
                        if (t == e[n])
                            return n;
                    return -1
                }
            }(),
            o = function() {
                var e = Array.prototype.forEach;
                return t(e) ? function(t, n) {
                    if (!t)
                        return;
                    if (!n)
                        return;
                    e.apply(t, [n])
                } : function(e, t) {
                    if (!e)
                        return;
                    if (!t)
                        return;
                    for (var n = 0, r = e.length; n < r; n++)
                        t(e[n], n)
                }
            }(),
            u = function() {
                var e = Array.prototype.filter;
                return t(e) ? function(t, n) {
                    return t ? n ? e.apply(t, [n]) : t : null
                } : function(e, t) {
                    if (!e)
                        return null;
                    if (!t)
                        return e;
                    var n = [],
                        r = 0,
                        i = e.length;
                    for (; r < i; r++)
                        t(e[r]) && n.push(e[r]);
                    return n
                }
            }(),
            a = function() {
                var e = Array.prototype.map;
                return t(e) ? function(t, n) {
                    return t ? n ? e.apply(t, [n]) : t : null
                } : function(e, t) {
                    if (!e)
                        return null;
                    if (!t)
                        return e;
                    var n = [],
                        r = 0,
                        i = e.length;
                    for (; r < i; r++)
                        n.push(t(e[r]));
                    return n
                }
            }(),
            f = function() {
                var e = Array.prototype.reduce;
                return t(e) ? function(t, n, r) {
                    return t ? n ? e.apply(t, [n, r]) : r : null
                } : function(e, t, n) {
                    if (!e)
                        return null;
                    if (!t)
                        return n;
                    var r = n,
                        i = 0,
                        s = e.length;
                    for (; i < s; i++)
                        r = t(r, e[i], i, e);
                    return r
                }
            }(),
            l = function() {
                var e = String.prototype.trim;
                return t(e) ? function(t) {
                    return t && e.apply(t)
                } : function(e) {
                    return e && e.replace(/(^\s+|\s+$)/g, "")
                }
            }(),
            d = t(Object.create) ? Object.create : function(e) {
                function t() {}
                return t.prototype = e, new t
            };
        e({
            aug: n,
            async: g,
            compact: r,
            forIn: s,
            forEach: o,
            filter: u,
            map: a,
            reduce: f,
            trim: l,
            indexOf: i,
            isNative: t,
            isObject: v,
            isEmptyObject: m,
            createObject: d,
            bind: p,
            toType: c,
            isType: h
        })
    });
    provide("util/events", function(e) {
        using("util/util", function(t) {
            var n = {
                bind: function(e, t) {
                    return this._handlers = this._handlers || {}, this._handlers[e] = this._handlers[e] || [], this._handlers[e].push(t)
                },
                unbind: function(e, n) {
                    if (!this._handlers[e])
                        return;
                    if (n) {
                        var r = t.indexOf(this._handlers[e], n);
                        r >= 0 && this._handlers[e].splice(r, 1)
                    } else
                        this._handlers[e] = []
                },
                trigger: function(e, n) {
                    var r = this._handlers && this._handlers[e];
                    n.type = e, t.forEach(r, function(e) {
                        t.async(t.bind(e, this, [n]))
                    })
                }
            };
            e({
                Emitter: n
            })
        })
    });
    provide("$xd/json2.js", function(exports) {
        window.JSON || (window.JSON = {}), function() {
            function f(e) {
                return e < 10 ? "0" + e : e
            }
            function quote(e) {
                return escapable.lastIndex = 0, escapable.test(e) ? '"' + e.replace(escapable, function(e) {
                    var t = meta[e];
                    return typeof t == "string" ? t : "\\u" + ("0000" + e.charCodeAt(0).toString(16)).slice(-4)
                }) + '"' : '"' + e + '"'
            }
            function str(e, t) {
                var n,
                    r,
                    i,
                    s,
                    o = gap,
                    u,
                    a = t[e];
                a && typeof a == "object" && typeof a.toJSON == "function" && (a = a.toJSON(e)), typeof rep == "function" && (a = rep.call(t, e, a));
                switch (typeof a) {
                case "string":
                    return quote(a);
                case "number":
                    return isFinite(a) ? String(a) : "null";
                case "boolean":
                case "null":
                    return String(a);
                case "object":
                    if (!a)
                        return "null";
                    gap += indent, u = [];
                    if (Object.prototype.toString.apply(a) === "[object Array]") {
                        s = a.length;
                        for (n = 0; n < s; n += 1)
                            u[n] = str(n, a) || "null";
                        return i = u.length === 0 ? "[]" : gap ? "[\n" + gap + u.join(",\n" + gap) + "\n" + o + "]" : "[" + u.join(",") + "]", gap = o, i
                    }
                    if (rep && typeof rep == "object") {
                        s = rep.length;
                        for (n = 0; n < s; n += 1)
                            r = rep[n], typeof r == "string" && (i = str(r, a), i && u.push(quote(r) + (gap ? ": " : ":") + i))
                    } else
                        for (r in a)
                            Object.hasOwnProperty.call(a, r) && (i = str(r, a), i && u.push(quote(r) + (gap ? ": " : ":") + i));
                    return i = u.length === 0 ? "{}" : gap ? "{\n" + gap + u.join(",\n" + gap) + "\n" + o + "}" : "{" + u.join(",") + "}", gap = o, i
                }
            }
            typeof Date.prototype.toJSON != "function" && (Date.prototype.toJSON = function(e) {
                return isFinite(this.valueOf()) ? this.getUTCFullYear() + "-" + f(this.getUTCMonth() + 1) + "-" + f(this.getUTCDate()) + "T" + f(this.getUTCHours()) + ":" + f(this.getUTCMinutes()) + ":" + f(this.getUTCSeconds()) + "Z" : null
            }, String.prototype.toJSON = Number.prototype.toJSON = Boolean.prototype.toJSON = function(e) {
                return this.valueOf()
            });
            var cx = /[\u0000\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,
                escapable = /[\\\"\x00-\x1f\x7f-\x9f\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,
                gap,
                indent,
                meta = {
                    "\b": "\\b",
                    "   ": "\\t",
                    "\n": "\\n",
                    "\f": "\\f",
                    "\r": "\\r",
                    '"': '\\"',
                    "\\": "\\\\"
                },
                rep;
            typeof JSON.stringify != "function" && (JSON.stringify = function(e, t, n) {
                var r;
                gap = "", indent = "";
                if (typeof n == "number")
                    for (r = 0; r < n; r += 1)
                        indent += " ";
                else
                    typeof n == "string" && (indent = n);
                rep = t;
                if (!t || typeof t == "function" || typeof t == "object" && typeof t.length == "number")
                    return str("", {
                        "": e
                    });
                throw new Error("JSON.stringify")
            }), typeof JSON.parse != "function" && (JSON.parse = function(text, reviver) {
                function walk(e, t) {
                    var n,
                        r,
                        i = e[t];
                    if (i && typeof i == "object")
                        for (n in i)
                            Object.hasOwnProperty.call(i, n) && (r = walk(i, n), r !== undefined ? i[n] = r : delete i[n]);
                    return reviver.call(e, t, i)
                }
                var j;
                cx.lastIndex = 0, cx.test(text) && (text = text.replace(cx, function(e) {
                    return "\\u" + ("0000" + e.charCodeAt(0).toString(16)).slice(-4)
                }));
                if (/^[\],:{}\s]*$/.test(text.replace(/\\(?:["\\\/bfnrt]|u[0-9a-fA-F]{4})/g, "@").replace(/"[^"\\\n\r]*"|true|false|null|-?\d+(?:\.\d*)?(?:[eE][+\-]?\d+)?/g, "]").replace(/(?:^|:|,)(?:\s*\[)+/g, "")))
                    return j = eval("(" + text + ")"), typeof reviver == "function" ? walk({
                        "": j
                    }, "") : j;
                throw new SyntaxError("JSON.parse")
            })
        }();
        exports();
        loadrunner.Script.loaded.push("$xd/json2.js")
    });
    provide("util/querystring", function(e) {
        function t(e) {
            return encodeURIComponent(e).replace(/\+/g, "%2B").replace(/'/g, "%27")
        }
        function n(e) {
            return decodeURIComponent(e)
        }
        function r(e) {
            var n = [],
                r;
            for (r in e)
                e[r] !== null && typeof e[r] != "undefined" && n.push(t(r) + "=" + t(e[r]));
            return n.sort().join("&")
        }
        function i(e) {
            var t = {},
                r,
                i,
                s,
                o;
            if (e) {
                r = e.split("&");
                for (o = 0; s = r[o]; o++)
                    i = s.split("="), i.length == 2 && (t[n(i[0])] = n(i[1]))
            }
            return t
        }
        function s(e, t) {
            var n = r(t);
            return n.length > 0 ? e.indexOf("?") >= 0 ? e + "&" + r(t) : e + "?" + r(t) : e
        }
        function o(e) {
            var t = e && e.split("?");
            return t.length == 2 ? i(t[1]) : {}
        }
        e({
            url: s,
            decodeURL: o,
            decode: i,
            encode: r,
            encodePart: t,
            decodePart: n
        })
    });
    provide("util/twitter", function(e) {
        using("util/querystring", function(t) {
            function u(e) {
                return typeof e == "string" && n.test(e) && RegExp.$1.length <= 20
            }
            function a(e) {
                if (u(e))
                    return RegExp.$1
            }
            function f(e) {
                var n = t.decodeURL(e);
                n.screen_name = a(e);
                if (n.screen_name)
                    return t.url("https://twitter.com/intent/user", n)
            }
            function l(e) {
                return typeof e == "string" && o.test(e)
            }
            function c(e, t) {
                t = t === undefined ? !0 : t;
                if (l(e))
                    return (t ? "#" : "") + RegExp.$1
            }
            function h(e) {
                return typeof e == "string" && r.test(e)
            }
            function p(e) {
                return h(e) && RegExp.$1
            }
            function d(e) {
                return i.test(e)
            }
            function v(e) {
                return s.test(e)
            }
            var n = /(?:^|(?:https?\:)?\/\/(?:www\.)?twitter\.com(?:\:\d+)?(?:\/intent\/(?:follow|user)\/?\?screen_name=|(?:\/#!)?\/))@?([\w]+)(?:\?|&|$)/i,
                r = /(?:^|(?:https?\:)?\/\/(?:www\.)?twitter\.com(?:\:\d+)?\/(?:#!\/)?[\w_]+\/status(?:es)?\/)(\d+)/i,
                i = /^http(s?):\/\/((www\.)?)twitter\.com\//,
                s = /^http(s?):\/\/pbs\.twimg\.com\//,
                o = /^#?([^.,<>!\s\/#\-\(\)\'\"]+)$/;
            e({
                isHashTag: l,
                hashTag: c,
                isScreenName: u,
                screenName: a,
                isStatus: h,
                status: p,
                intentForProfileURL: f,
                isTwitterURL: d,
                isTwimgURL: v,
                regexen: {
                    profile: n
                }
            })
        })
    });
    provide("util/uri", function(e) {
        using("util/querystring", "util/util", "util/twitter", function(t, n, r) {
            function i(e, t) {
                var n,
                    r;
                return t = t || location, /^https?:\/\//.test(e) ? e : /^\/\//.test(e) ? t.protocol + e : (n = t.host + (t.port.length ? ":" + t.port : ""), e.indexOf("/") !== 0 && (r = t.pathname.split("/"), r.pop(), r.push(e), e = "/" + r.join("/")), [t.protocol, "//", n, e].join(""))
            }
            function s() {
                var e = document.getElementsByTagName("link"),
                    t = 0,
                    n;
                for (; n = e[t]; t++)
                    if (n.rel == "canonical")
                        return i(n.href)
            }
            function o() {
                var e = document.getElementsByTagName("a"),
                    t = document.getElementsByTagName("link"),
                    n = [e, t],
                    i,
                    s,
                    o = 0,
                    u = 0,
                    a = /\bme\b/,
                    f;
                for (; i = n[o]; o++)
                    for (u = 0; s = i[u]; u++)
                        if (a.test(s.rel) && (f = r.screenName(s.href)))
                            return f
            }
            e({
                absolutize: i,
                getCanonicalURL: s,
                getScreenNameFromPage: o
            })
        })
    });
    provide("util/typevalidator", function(e) {
        using("util/util", function(t) {
            function n(e) {
                return e !== undefined && e !== null && e !== ""
            }
            function r(e) {
                return s(e) && e % 1 === 0
            }
            function i(e) {
                return s(e) && !r(e)
            }
            function s(e) {
                return n(e) && !isNaN(e)
            }
            function o(e) {
                return n(e) && t.toType(e) == "array"
            }
            function u(e) {
                if (!n(e))
                    return !1;
                switch (e) {
                case "on":
                case "ON":
                case "true":
                case "TRUE":
                    return !0;
                case "off":
                case "OFF":
                case "false":
                case "FALSE":
                    return !1;
                default:
                    return !!e
                }
            }
            function a(e) {
                if (s(e))
                    return e
            }
            function f(e) {
                if (i(e))
                    return e
            }
            function l(e) {
                if (r(e))
                    return e
            }
            e({
                hasValue: n,
                isInt: r,
                isFloat: i,
                isNumber: s,
                isArray: o,
                asInt: l,
                asFloat: f,
                asNumber: a,
                asBoolean: u
            })
        })
    });
    provide("tfw/util/globals", function(e) {
        using("util/typevalidator", function(t) {
            function r() {
                var e = document.getElementsByTagName("meta"),
                    t,
                    r,
                    i = 0;
                n = {};
                for (; t = e[i]; i++) {
                    if (!/^twitter:/.test(t.name))
                        continue;
                    r = t.name.replace(/^twitter:/, ""), n[r] = t.content
                }
            }
            function i(e) {
                return n[e]
            }
            function s(e) {
                return t.asBoolean(e) && (n.dnt = !0), t.asBoolean(n.dnt)
            }
            var n;
            r(), e({
                init: r,
                val: i,
                dnt: s
            })
        })
    });
    provide("util/logger", function(e) {
        function n(e, n, r, i, s) {
            window[t] && window[t].log && window[t].log(e, n, r, i, s)
        }
        function r(e, n, r, i, s) {
            window[t] && window[t].warn && window[t].warn(e, n, r, i, s)
        }
        function i(e, n, r, i, s) {
            window[t] && window[t].error && window[t].error(e, n, r, i, s)
        }
        var t = ["con", "sole"].join("");
        e({
            info: n,
            warn: r,
            error: i
        })
    });
    provide("util/domready", function(e) {
        function l() {
            t = 1;
            for (var e = 0, r = n.length; e < r; e++)
                n[e]()
        }
        var t = 0,
            n = [],
            r,
            i,
            s = !1,
            o = document.createElement("a"),
            u = "DOMContentLoaded",
            a = "addEventListener",
            f = "onreadystatechange";
        /^loade|c/.test(document.readyState) && (t = 1), document[a] && document[a](u, i = function() {
            document.removeEventListener(u, i, s), l()
        }, s), o.doScroll && document.attachEvent(f, r = function() {
            /^c/.test(document.readyState) && (document.detachEvent(f, r), l())
        });
        var c = o.doScroll ? function(e) {
            self != top ? t ? e() : n.push(e) : !function() {
                try {
                    o.doScroll("left")
                } catch (t) {
                    return setTimeout(function() {
                        c(e)
                    }, 50)
                }
                e()
            }()
        } : function(e) {
            t ? e() : n.push(e)
        };
        e(c)
    });
    provide("util/env", function(e) {
        using("util/domready", "util/typevalidator", "util/logger", "tfw/util/globals", function(t, n, r, i) {
            function f(e) {
                return e = e || window, e.devicePixelRatio ? e.devicePixelRatio >= 1.5 : e.matchMedia ? e.matchMedia("only screen and (min-resolution: 144dpi)").matches : !1
            }
            function l(e) {
                return e = e || s, /(Trident|MSIE \d)/.test(e)
            }
            function c(e) {
                return e = e || s, /MSIE 6/.test(e)
            }
            function h(e) {
                return e = e || s, /MSIE 7/.test(e)
            }
            function p(e) {
                return e = e || s, /MSIE 9/.test(e)
            }
            function d(e) {
                return e = e || s, /(iPad|iPhone|iPod)/.test(e)
            }
            function v(e) {
                return e = e || s, /^Mozilla\/5\.0 \(Linux; (U; )?Android/.test(e)
            }
            function m() {
                return o
            }
            function g(e, t) {
                return e = e || window, t = t || s, e.postMessage && (!l(t) || !e.opener)
            }
            function y(e) {
                e = e || navigator;
                try {
                    return !!e.plugins["Shockwave Flash"] || !!(new ActiveXObject("ShockwaveFlash.ShockwaveFlash"))
                } catch (t) {
                    return !1
                }
            }
            function b(e, t, n) {
                return e = e || window, t = t || navigator, n = n || s, "ontouchstart" in e || /Opera Mini/.test(n) || t.msMaxTouchPoints > 0
            }
            function w() {
                var e = document.body.style;
                return e.transition !== undefined || e.webkitTransition !== undefined || e.mozTransition !== undefined || e.oTransition !== undefined || e.msTransition !== undefined
            }
            var s = window.navigator.userAgent,
                o = !1,
                u = !1,
                a = "twitter-csp-test";
            window.twttr = window.twttr || {}, twttr.verifyCSP = function(e) {
                var t = document.getElementById(a);
                u = !0, o = !!e, t && t.parentNode.removeChild(t)
            }, t(function() {
                var e;
                if (c() || h())
                    return o = !1;
                if (n.asBoolean(i.val("widgets:csp")))
                    return o = !0;
                e = document.createElement("script"), e.id = a, e.text = "twttr.verifyCSP(false);", document.body.appendChild(e), window.setTimeout(function() {
                    if (u)
                        return;
                    r.warn('TWITTER: Content Security Policy restrictions may be applied to your site. Add <meta name="twitter:widgets:csp" content="on"> to supress this warning.'), r.warn("TWITTER: Please note: Not all embedded timeline and embedded Tweet functionality is supported when CSP is applied.")
                }, 5e3)
            }), e({
                retina: f,
                anyIE: l,
                ie6: c,
                ie7: h,
                ie9: p,
                ios: d,
                android: v,
                cspEnabled: m,
                flashEnabled: y,
                canPostMessage: g,
                touch: b,
                cssTransitions: w
            })
        })
    });
    provide("dom/delegate", function(e) {
        using("util/env", function(t) {
            function i(e) {
                var t = e.getAttribute("data-twitter-event-id");
                return t ? t : (e.setAttribute("data-twitter-event-id", ++r), r)
            }
            function s(e, t, n) {
                var r = 0,
                    i = e && e.length || 0;
                for (r = 0; r < i; r++)
                    e[r].call(t, n)
            }
            function o(e, t, n) {
                var r = n || e.target || e.srcElement,
                    i = r.className.split(" "),
                    u = 0,
                    a,
                    f = i.length;
                for (; u < f; u++)
                    s(t["." + i[u]], r, e);
                s(t[r.tagName], r, e);
                if (e.cease)
                    return;
                r !== this && o.call(this, e, t, r.parentElement || r.parentNode)
            }
            function u(e, t, n) {
                if (e.addEventListener) {
                    e.addEventListener(t, function(r) {
                        o.call(e, r, n[t])
                    }, !1);
                    return
                }
                e.attachEvent && e.attachEvent("on" + t, function() {
                    o.call(e, e.ownerDocument.parentWindow.event, n[t])
                })
            }
            function a(e, t, r, s) {
                var o = i(e);
                n[o] = n[o] || {}, n[o][t] || (n[o][t] = {}, u(e, t, n[o])), n[o][t][r] = n[o][t][r] || [], n[o][t][r].push(s)
            }
            function f(e, t, n) {
                e.addEventListener ? e.addEventListener(t, n, !1) : e.attachEvent("on" + t, function() {
                    n(window.event)
                })
            }
            function l(e, t, r) {
                var s = i(t),
                    u = n[s] && n[s];
                o.call(t, {
                    target: r
                }, u[e])
            }
            function c(e) {
                return p(e), h(e), !1
            }
            function h(e) {
                e && e.preventDefault ? e.preventDefault() : e.returnValue = !1
            }
            function p(e) {
                e && (e.cease = !0) && e.stopPropagation ? e.stopPropagation() : e.cancelBubble = !0
            }
            var n = {},
                r = -1;
            e({
                stop: c,
                stopPropagation: p,
                preventDefault: h,
                delegate: a,
                on: f,
                simulate: l
            })
        })
    });
    provide("tfw/util/article", function(e) {
        using("dom/delegate", "tfw/util/globals", "util/uri", "$xd/json2.js", function(t, n, r) {
            function o() {
                i = r.getCanonicalURL() || "" + document.location;
                if (!window.top.postMessage)
                    return;
                if (window == window.top) {
                    t.on(window, "message", function(e) {
                        var t;
                        if (e.data && e.data[0] != "{")
                            return;
                        try {
                            t = JSON.parse(e.data)
                        } catch (r) {}
                        t && t.name == "twttr:private:requestArticleUrl" && e.source.postMessage(JSON.stringify({
                            name: "twttr:private:provideArticleUrl",
                            data: {
                                url: i,
                                dnt: n.dnt()
                            }
                        }), "*")
                    });
                    return
                }
                t.on(window, "message", function(e) {
                    var t;
                    if (e.data && e.data[0] != "{")
                        return;
                    try {
                        t = JSON.parse(e.data)
                    } catch (r) {}
                    t && t.name == "twttr:private:provideArticleUrl" && (i = t.data && t.data.url, n.dnt(t.data.dnt), s = document.location.href)
                }), window.top.postMessage(JSON.stringify({
                    name: "twttr:private:requestArticleUrl"
                }), "*")
            }
            var i,
                s = "";
            o(), e({
                url: function() {
                    return i
                },
                frameUrl: function() {
                    return s
                }
            })
        })
    });
    provide("dom/get", function(e) {
        using("util/util", function(t) {
            function r(e, t, r) {
                return n(e, t, r, 1)[0]
            }
            function i(e, n, r) {
                var s = n && n.parentNode,
                    o;
                if (!s || s === r)
                    return;
                return s.tagName == e ? s : (o = s.className.split(" "), 0 === e.indexOf(".") && ~t.indexOf(o, e.slice(1)) ? s : i(e, s, r))
            }
            var n = function() {
                var e = document.getElementsByClassName;
                return t.isNative(e) ? function(n, r, i, s) {
                    var o = r ? r.getElementsByClassName(n) : e.call(document, n),
                        u = t.filter(o, function(e) {
                            return !i || e.tagName.toLowerCase() == i.toLowerCase()
                        });
                    return [].slice.call(u, 0, s || u.length)
                } : function(e, n, r, i) {
                    var s,
                        o,
                        u = [],
                        a,
                        f,
                        l,
                        c,
                        h,
                        p;
                    n = n || document, a = e.split(" "), c = a.length, s = n.getElementsByTagName(r || "*"), p = s.length;
                    for (l = 0; l < c && p > 0; l++) {
                        u = [], f = a[l];
                        for (h = 0; h < p; h++) {
                            o = s[h], ~t.indexOf(o.className.split(" "), f) && u.push(o);
                            if (l + 1 == c && u.length === i)
                                break
                        }
                        s = u, p = s.length
                    }
                    return u
                }
            }();
            e({
                all: n,
                one: r,
                ancestor: i
            })
        })
    });
    provide("dom/classname", function(e) {
        function t(e) {
            return new RegExp("\\b" + e + "\\b", "g")
        }
        function n(e, n) {
            if (e.classList) {
                e.classList.add(n);
                return
            }
            t(n).test(e.className) || (e.className += " " + n)
        }
        function r(e, n) {
            if (e.classList) {
                e.classList.remove(n);
                return
            }
            e.className = e.className.replace(t(n), " ")
        }
        function i(e, t, i) {
            return e.classList && e.classList.toggle ? e.classList.toggle(t, i) : (i ? n(e, t) : r(e, t), i)
        }
        function s(e, i, s) {
            if (e.classList && o(e, i)) {
                r(e, i), n(e, s);
                return
            }
            e.className = e.className.replace(t(i), s)
        }
        function o(e, n) {
            return e.classList ? e.classList.contains(n) : t(n).test(e.className)
        }
        e({
            add: n,
            remove: r,
            replace: s,
            toggle: i,
            present: o
        })
    });
    provide("util/throttle", function(e) {
        function t(e, t, n) {
            function o() {
                var n = +(new Date);
                window.clearTimeout(s);
                if (n - i > t) {
                    i = n, e.call(r);
                    return
                }
                s = window.setTimeout(o, t)
            }
            var r = n || this,
                i = 0,
                s;
            return o
        }
        e(t)
    });
    provide("util/css", function(e) {
        using("util/util", function(t) {
            e({
                sanitize: function(e, n, r) {
                    var i = /^[\w ,%\/"'\-_#]+$/,
                        s = e && t.map(e.split(";"), function(e) {
                            return t.map(e.split(":").slice(0, 2), function(e) {
                                return t.trim(e)
                            })
                        }),
                        o = 0,
                        u,
                        a = [],
                        f = r ? "!important" : "";
                    n = n || /^(font|text\-|letter\-|color|line\-)[\w\-]*$/;
                    for (; s && (u = s[o]); o++)
                        u[0].match(n) && u[1].match(i) && a.push(u.join(":") + f);
                    return a.join(";")
                }
            })
        })
    });
    provide("tfw/util/params", function(e) {
        using("util/querystring", "util/twitter", function(t, n) {
            e(function(e, r) {
                return function(i) {
                    var s,
                        o = "data-tw-params",
                        u,
                        a = i.innerHTML;
                    if (!i)
                        return;
                    if (!n.isTwitterURL(i.href))
                        return;
                    if (i.getAttribute(o))
                        return;
                    i.setAttribute(o, !0);
                    if (typeof r == "function") {
                        s = r.call(this, i);
                        for (u in s)
                            s.hasOwnProperty(u) && (e[u] = s[u])
                    }
                    i.href = t.url(i.href, e)
                }
            })
        })
    });
    provide("util/iframe", function(e) {
        using("util/util", function(t) {
            e(function(e, n, r) {
                var i;
                r = r || document, e = e || {}, n = n || {};
                if (e.name) {
                    try {
                        i = r.createElement('<iframe name="' + e.name + '"></iframe>')
                    } catch (s) {
                        i = r.createElement("iframe"), i.name = e.name
                    }
                    delete e.name
                } else
                    i = r.createElement("iframe");
                return e.id && (i.id = e.id, delete e.id), i.allowtransparency = "true", i.scrolling = "no", i.setAttribute("frameBorder", 0), i.setAttribute("allowTransparency", !0), t.forIn(e, function(e, t) {
                    i.setAttribute(e, t)
                }), t.forIn(n, function(e, t) {
                    i.style[e] = t
                }), i
            })
        })
    });
    provide("util/params", function(e) {
        using("util/querystring", function(t) {
            var n = function(e) {
                    var n = e.search.substr(1);
                    return t.decode(n)
                },
                r = function(e) {
                    var n = e.href,
                        r = n.indexOf("#"),
                        i = r < 0 ? "" : n.substring(r + 1);
                    return t.decode(i)
                },
                i = function(e) {
                    var t = {},
                        i = n(e),
                        s = r(e);
                    for (var o in i)
                        i.hasOwnProperty(o) && (t[o] = i[o]);
                    for (var o in s)
                        s.hasOwnProperty(o) && (t[o] = s[o]);
                    return t
                };
            e({
                combined: i,
                fromQuery: n,
                fromFragment: r
            })
        })
    });
    provide("tfw/util/env", function(e) {
        using("util/params", function(t) {
            function r() {
                var e = 36e5,
                    r = t.combined(document.location)._;
                return n !== undefined ? n : (n = !1, r && /^\d+$/.test(r) && (n = +(new Date) - parseInt(r) < e), n)
            }
            var n;
            e({
                isDynamicWidget: r
            })
        })
    });
    provide("util/promise", function(e) {
        using("util/util", function(t) {
            var n = function(e) {
                    try {
                        var t = e.then;
                        if (typeof t == "function")
                            return !0
                    } catch (n) {}
                    return !1
                },
                r = function(e) {
                    Error.call(this, e)
                };
            r.prototype = t.createObject(Error.prototype);
            var i = function() {
                    var e = [];
                    return e.pump = function(n) {
                        t.async(function() {
                            var t = e.length,
                                r = 0;
                            while (r < t)
                                r++, e.shift()(n)
                        })
                    }, e
                },
                s = function(e, r, i, s, o, u) {
                    var a = !1,
                        f = this,
                        l = function(e) {
                            t.async(function() {
                                u("fulfilled"), s(e), r.pump(e)
                            })
                        },
                        c = function(e) {
                            t.async(function() {
                                u("rejected"), o(e), i.pump(e)
                            })
                        },
                        h = function(e) {
                            if (n(e)) {
                                e.then(h, c);
                                return
                            }
                            l(e)
                        },
                        p = function(e, t) {
                            return function(t) {
                                a || (a = !0, e(t))
                            }
                        };
                    this.resolve = p(h, "resolve"), this.fulfill = p(l, "fulfill"), this.reject = p(c, "reject"), this.cancel = function() {
                        f.reject(new Error("Cancel"))
                    }, this.timeout = function() {
                        f.reject(new Error("Timeout"))
                    }, u("pending")
                },
                o = function(e) {
                    var t = new i,
                        n = new i,
                        r,
                        o,
                        u = "pending";
                    this._addAcceptCallback = function(e) {
                        t.push(e), u == "fulfilled" && t.pump(r)
                    }, this._addRejectCallback = function(e) {
                        n.push(e), u == "rejected" && n.pump(o)
                    };
                    var a = new s(this, t, n, function(e) {
                        r = e
                    }, function(e) {
                        o = e
                    }, function(e) {
                        u = e
                    });
                    try {
                        e && e(a)
                    } catch (f) {
                        a.reject(f)
                    }
                },
                u = function(e) {
                    return typeof e == "function"
                },
                a = function(e, n, r) {
                    return u(e) ? function() {
                        try {
                            var t = e.apply(null, arguments);
                            n.resolve(t)
                        } catch (r) {
                            n.reject(r)
                        }
                    } : t.bind(n[r], n)
                },
                f = function(e, t, n) {
                    return u(e) && n._addAcceptCallback(e), u(t) && n._addRejectCallback(t), n
                };
            t.aug(o.prototype, {
                then: function(e, t) {
                    var n = this;
                    return new o(function(r) {
                        f(a(e, r, "resolve"), a(t, r, "reject"), n)
                    })
                },
                "catch": function(e) {
                    var t = this;
                    return new o(function(n) {
                        f(null, a(e, n, "reject"), t)
                    })
                }
            }), o.isThenable = n;
            var l = function(e) {
                return t.map(e, o.resolve)
            };
            o.any = function() {
                var e = l(arguments);
                return new o(function(n) {
                    if (!e.length)
                        n.reject("No futures passed to Promise.any()");
                    else {
                        var r = !1,
                            i = function(e) {
                                if (r)
                                    return;
                                r = !0, n.resolve(e)
                            },
                            s = function(e) {
                                if (r)
                                    return;
                                r = !0, n.reject(e)
                            };
                        t.forEach(e, function(e, t) {
                            e.then(i, s)
                        })
                    }
                })
            }, o.every = function() {
                var e = l(arguments);
                return new o(function(n) {
                    if (!e.length)
                        n.reject("No futures passed to Promise.every()");
                    else {
                        var r = new Array(e.length),
                            i = 0,
                            s = function(t, s) {
                                i++, r[t] = s, i == e.length && n.resolve(r)
                            };
                        t.forEach(e, function(e, r) {
                            e.then(t.bind(s, null, [r]), n.reject)
                        })
                    }
                })
            }, o.some = function() {
                var e = l(arguments);
                return new o(function(n) {
                    if (!e.length)
                        n.reject("No futures passed to Promise.some()");
                    else {
                        var r = 0,
                            i = function(t) {
                                r++, r == e.length && n.reject()
                            };
                        t.forEach(e, function(e, t) {
                            e.then(n.resolve, i)
                        })
                    }
                })
            }, o.fulfill = function(e) {
                return new o(function(t) {
                    t.fulfill(e)
                })
            }, o.resolve = function(e) {
                return new o(function(t) {
                    t.resolve(e)
                })
            }, o.reject = function(e) {
                return new o(function(t) {
                    t.reject(e)
                })
            }, e(o)
        })
    });
    provide("util/donottrack", function(e) {
        using("tfw/util/globals", function(t) {
            e(function(e, n) {
                var r = /\.(gov|mil)(:\d+)?$/i,
                    i = /https?:\/\/([^\/]+).*/i;
                return e = e || document.referrer, e = i.test(e) && RegExp.$1, n = n || document.location.host, t.dnt() ? !0 : r.test(n) ? !0 : e && r.test(e) ? !0 : document.navigator ? document.navigator["doNotTrack"] == 1 : navigator ? navigator["doNotTrack"] == 1 || navigator["msDoNotTrack"] == 1 : !1
            })
        })
    });
    provide("sandbox/baseframe", function(e) {
        using("util/domready", "util/env", "util/iframe", "util/promise", "util/util", function(t, n, r, i, s) {
            function u(e, t, n, o) {
                var u;
                this.readyPromise = new i(s.bind(function(e) {
                    this.resolver = e
                }, this)), this.attrs = e || {}, this.styles = t || {}, this.appender = n || function(e) {
                    document.body.appendChild(e)
                }, this.layout = o || function(e) {
                    return new i(function(t) {
                        return t.fulfill(e())
                    })
                }, this.frame = u = r(this.attrs, this.styles), u.onreadystatechange = u.onload = this.getCallback(this.onLoad), this.layout(s.bind(function() {
                    this.appender(u)
                }, this))
            }
            var o = 0;
            window.twttr = window.twttr || {}, window.twttr.sandbox = window.twttr.sandbox || {}, u.prototype.getCallback = function(e) {
                var t = this,
                    n = !1;
                return function() {
                    n || (n = !0, e.call(t))
                }
            }, u.prototype.registerCallback = function(e) {
                var t = "cb" + o++;
                return window.twttr.sandbox[t] = e, t
            }, u.prototype.onLoad = function() {
                try {
                    this.document = this.frame.contentWindow.document
                } catch (e) {
                    this.setDocDomain();
                    return
                }
                this.writeStandardsDoc(), this.resolver.fulfill(this)
            }, u.prototype.ready = function() {
                return this.readyPromise
            }, u.prototype.setDocDomain = function() {
                var e = r(this.attrs, this.styles),
                    t = this.registerCallback(this.getCallback(this.onLoad));
                e.src = ["javascript:", 'document.write("");', "try { window.parent.document; }", "catch (e) {", 'document.domain="' + document.domain + '";', "}", 'window.parent.twttr.sandbox["' + t + '"]();'].join(""), this.layout(s.bind(function() {
                    this.frame.parentNode.removeChild(this.frame), this.frame = null, this.appender ? this.appender(e) : document.body.appendChild(e), this.frame = e
                }, this))
            }, u.prototype.writeStandardsDoc = function() {
                if (!n.anyIE() || n.cspEnabled())
                    return;
                var e = ["<!DOCTYPE html>", "<html>", "<head>", "<scr", "ipt>", "try { window.parent.document; }", 'catch (e) {document.domain="' + document.domain + '";}', "</scr", "ipt>", "</head>", "<body></body>", "</html>"].join("");
                this.document.write(e), this.document.close()
            }, e(u)
        })
    });
    provide("sandbox/minimal", function(e) {
        using("sandbox/baseframe", "util/env", "util/promise", "util/util", function(t, n, r, i) {
            function s(e, t) {
                if (!e)
                    return;
                this._frame = e, this._win = e.contentWindow, this._doc = this._win.document, this._body = this._doc.body, this._head = this._body.parentNode.children[0], this.layout = t
            }
            i.aug(s.prototype, {
                createElement: function(e) {
                    return this._doc.createElement(e)
                },
                createDocumentFragment: function() {
                    return this._doc.createDocumentFragment()
                },
                appendChild: function(e) {
                    return this.layout(i.bind(function() {
                        return this._body.appendChild(e)
                    }, this))
                },
                setBaseTarget: function(e) {
                    var t = this._doc.createElement("base");
                    return t.target = e, this.layout(i.bind(function() {
                        return this._head.appendChild(t)
                    }, this))
                },
                setTitle: function(e) {
                    if (!e)
                        return;
                    this._frame.title = e
                },
                element: function() {
                    return this._frame
                },
                document: function() {
                    return this._doc
                }
            }), s.createSandbox = function(e, n, r, i) {
                var o = new t(e, n, r, i);
                return o.ready().then(function(e) {
                    return new s(e.frame, e.layout)
                })
            }, e(s)
        })
    });
    provide("dom/cookie", function(e) {
        using("util/util", function(t) {
            e(function(e, n, r) {
                var i = t.aug({}, r);
                if (arguments.length > 1 && String(n) !== "[object Object]") {
                    if (n === null || n === undefined)
                        i.expires = -1;
                    if (typeof i.expires == "number") {
                        var s = i.expires,
                            o = new Date((new Date).getTime() + s * 60 * 1e3);
                        i.expires = o
                    }
                    return n = String(n), document.cookie = [encodeURIComponent(e), "=", i.raw ? n : encodeURIComponent(n), i.expires ? "; expires=" + i.expires.toUTCString() : "", i.path ? "; path=" + i.path : "", i.domain ? "; domain=" + i.domain : "", i.secure ? "; secure" : ""].join("")
                }
                i = n || {};
                var u,
                    a = i.raw ? function(e) {
                        return e
                    } : decodeURIComponent;
                return (u = (new RegExp("(?:^|; )" + encodeURIComponent(e) + "=([^;]*)")).exec(document.cookie)) ? a(u[1]) : null
            })
        })
    });
    provide("tfw/util/tracking", function(e) {
        using("dom/cookie", "dom/delegate", "sandbox/minimal", "util/donottrack", "util/promise", "util/querystring", "tfw/util/env", "util/iframe", "util/util", "$xd/json2.js", function(t, n, r, i, s, o, u, a, f) {
            function E() {
                return y ? y : y = r.createSandbox({
                    id: "rufous-sandbox"
                }, {
                    display: "none"
                }).then(f.bind(function(e) {
                    g = e, p = _(), d = D();
                    while (v[0])
                        k.apply(this, v.shift());
                    return m ? L() : [p, d]
                }, this))
            }
            function S(e, t, n, r) {
                var i = !f.isObject(e),
                    s = t ? !f.isObject(t) : !1,
                    o,
                    u;
                if (i || s)
                    return;
                o = O(e), u = M(t, !!n, !!r), C(o, u, !0)
            }
            function x(e, t, n, r, i) {
                var s = T(e.target || e.srcElement);
                s.action = i || "click", S(s, t, n, r)
            }
            function T(e, t) {
                var n;
                return t = t || {}, !e || e.nodeType !== 1 ? t : ((n = e.getAttribute("data-scribe")) && f.forEach(n.split(" "), function(e) {
                    var n = f.trim(e).split(":"),
                        r = n[0],
                        i = n[1];
                    r && i && !t[r] && (t[r] = i)
                }), T(e.parentNode, t))
            }
            function N(e, t, n) {
                var r = l + t;
                if (!e)
                    return;
                return e[r] = n, e
            }
            function C(e, t, n) {
                var r,
                    i,
                    s,
                    u,
                    a;
                if (!f.isObject(e) || !f.isObject(t))
                    return;
                s = f.aug({}, t, {
                    event_namespace: e
                }), n ? (u = {
                    l: B(s)
                }, s.dnt && (u.dnt = 1), P(o.url(b, u))) : (r = p.firstChild, r.value = +(+r.value || s.dnt || 0), a = B(s), i = g.createElement("input"), i.type = "hidden", i.name = "l", i.value = a, p.appendChild(i))
            }
            function k(e, t, n, r) {
                var i = !f.isObject(e),
                    s = t ? !f.isObject(t) : !1,
                    o,
                    u;
                if (i || s)
                    return;
                if (!g || !p) {
                    v.push([e, t, n, r]);
                    return
                }
                o = O(e), u = M(t, !!n, !!r), C(o, u)
            }
            function L() {
                if (!p)
                    return m = !0, y || s.reject();
                if (p.children.length <= 2)
                    return s.reject();
                var e = s.every(g.appendChild(p), g.appendChild(d)).then(function(e) {
                    var t = e[0],
                        r = e[1];
                    return n.on(r, "load", function() {
                        window.setTimeout(A(t, r), 0)
                    }), t.submit(), e
                });
                return p = _(), d = D(), e
            }
            function A(e, t) {
                return function() {
                    var n = e.parentNode;
                    if (!n)
                        return;
                    n.removeChild(e), n.removeChild(t)
                }
            }
            function O(e) {
                return f.aug({
                    client: "tfw"
                }, e || {})
            }
            function M(e, t, n) {
                var r = {
                        _category_: "tfw_client_event"
                    },
                    s,
                    o;
                t = !!t, n = !!n, s = f.aug(r, e || {}), o = s.widget_origin || document.referrer, s.format_version = 1, s.triggered_on = s.triggered_on || +(new Date), t || (s.widget_origin = o);
                if (n || i(o))
                    s.dnt = !0, H(s);
                return s
            }
            function _() {
                var e = g.createElement("form"),
                    t = g.createElement("input"),
                    n = g.createElement("input");
                return h++, e.action = b, e.method = "POST", e.target = "rufous-frame-" + h, e.id = "rufous-form-" + h, t.type = "hidden", t.name = "dnt", t.value = 0, n.type = "hidden", n.name = "tfw_redirect", n.value = w, e.appendChild(t), e.appendChild(n), e
            }
            function D() {
                var e = "rufous-frame-" + h;
                return a({
                    id: e,
                    name: e,
                    width: 0,
                    height: 0,
                    border: 0
                }, {
                    display: "none"
                }, g.document())
            }
            function P(e) {
                var t = new Image;
                t.src = e
            }
            function H(e) {
                f.forIn(e, function(t) {
                    ~f.indexOf(c, t) && delete e[t]
                })
            }
            function B(e) {
                var t = Array.prototype.toJSON,
                    n;
                return delete Array.prototype.toJSON, n = JSON.stringify(e), t && (Array.prototype.toJSON = t), n
            }
            var l = "twttr_",
                c = ["hask", "li", "logged_in", "pid", "user_id", "guest_id", l + "hask", l + "li", l + "pid"],
                h = 0,
                p,
                d,
                v = [],
                m,
                g,
                y,
                b = "https://twitter.com/i/jot",
                w = "https://platform.twitter.com/jot.html";
            e({
                enqueue: k,
                flush: L,
                initPostLogging: E,
                scribeInteraction: x,
                extractTermsFromDOM: T,
                addPixel: S,
                addVar: N
            })
        })
    });
    provide("tfw/util/data", function(e) {
        using("util/logger", "util/util", "util/querystring", function(t, n, r) {
            function c(e) {
                return function(n) {
                    n.error ? e.error && e.error(n) : n.headers && n.headers.status != 200 ? (e.error && e.error(n), t.warn(n.headers.message)) : e.success && e.success(n), e.complete && e.complete(n), h(e)
                }
            }
            function h(e) {
                var t = e.script;
                t && (t.onload = t.onreadystatechange = null, t.parentNode && t.parentNode.removeChild(t), e.script = undefined, t = undefined), e.callbackName && twttr.tfw.callbacks[e.callbackName] && delete twttr.tfw.callbacks[e.callbackName]
            }
            function p(e) {
                var t = {};
                return e.success && n.isType("function", e.success) && (t.success = e.success), e.error && n.isType("function", e.error) && (t.error = e.error), e.complete && n.isType("function", e.complete) && (t.complete = e.complete), t
            }
            window.twttr = window.twttr || {}, twttr.tfw = twttr.tfw || {}, twttr.tfw.callbacks = twttr.tfw.callbacks || {};
            var i = "twttr.tfw.callbacks",
                s = twttr.tfw.callbacks,
                o = "cb",
                u = 0,
                a = !1,
                f = {},
                l = {
                    tweets: "https://syndication.twitter.com/tweets.json",
                    timeline: "https://cdn.syndication.twimg.com/widgets/timelines/",
                    timelinePoll: "https://syndication.twitter.com/widgets/timelines/paged/",
                    timelinePreview: "https://syndication.twitter.com/widgets/timelines/preview/"
                };
            twttr.widgets && twttr.widgets.endpoints && n.aug(l, twttr.widgets.endpoints), f.jsonp = function(e, t, n) {
                var f = n || o + u,
                    l = i + "." + f,
                    h = document.createElement("script"),
                    p = {
                        callback: l,
                        suppress_response_codes: !0
                    };
                s[f] = c(t);
                if (a || !/^https?\:$/.test(window.location.protocol))
                    e = e.replace(/^\/\//, "https://");
                h.src = r.url(e, p), h.async = "async", document.body.appendChild(h), t.script = h, t.callbackName = f, n || u++
            }, f.config = function(e) {
                if (e.forceSSL === !0 || e.forceSSL === !1)
                    a = e.forceSSL
            }, f.tweets = function(e) {
                var t = arguments[0],
                    n = p(t),
                    i = {
                        ids: e.ids.join(","),
                        lang: e.lang
                    },
                    s = r.url(l.tweets, i);
                this.jsonp(s, n)
            }, f.timeline = function(e) {
                var t = arguments[0],
                    i = p(t),
                    s,
                    o = 9e5,
                    u = Math.floor(+(new Date) / o),
                    a = {
                        lang: e.lang,
                        t: u,
                        domain: window.location.host,
                        dnt: e.dnt,
                        override_type: e.overrideType,
                        override_id: e.overrideId,
                        override_name: e.overrideName,
                        override_owner_id: e.overrideOwnerId,
                        override_owner_name: e.overrideOwnerName,
                        with_replies: e.withReplies
                    };
                n.compact(a), s = r.url(l.timeline + e.id, a), this.jsonp(s, i, "tl_" + e.id + "_" + e.instanceId)
            }, f.timelinePoll = function(e) {
                var t = arguments[0],
                    i = p(t),
                    s = {
                        lang: e.lang,
                        since_id: e.sinceId,
                        max_id: e.maxId,
                        min_position: e.minPosition,
                        max_position: e.maxPosition,
                        domain: window.location.host,
                        dnt: e.dnt,
                        override_type: e.overrideType,
                        override_id: e.overrideId,
                        override_name: e.overrideName,
                        override_owner_id: e.overrideOwnerId,
                        override_owner_name: e.overrideOwnerName,
                        with_replies: e.withReplies
                    },
                    o;
                n.compact(s), o = r.url(l.timelinePoll + e.id, s), this.jsonp(o, i, "tlPoll_" + e.id + "_" + e.instanceId + "_" + (e.sinceId || e.maxId || e.maxPosition || e.minPosition))
            }, f.timelinePreview = function(e) {
                var t = arguments[0],
                    n = p(t),
                    i = e.params,
                    s = r.url(l.timelinePreview, i);
                this.jsonp(s, n)
            }, e(f)
        })
    });
    provide("anim/transition", function(e) {
        function t(e, t) {
            var n;
            return t = t || window, n = t.requestAnimationFrame || t.webkitRequestAnimationFrame || t.mozRequestAnimationFrame || t.msRequestAnimationFrame || t.oRequestAnimationFrame || function(n) {
                t.setTimeout(function() {
                    e(+(new Date))
                }, 1e3 / 60)
            }, n(e)
        }
        function n(e, t) {
            return Math.sin(Math.PI / 2 * t) * e
        }
        function r(e, n, r, i, s) {
            function a() {
                var u = +(new Date),
                    f = u - o,
                    l = Math.min(f / r, 1),
                    c = i ? i(n, l) : n * l;
                e(c);
                if (l == 1)
                    return;
                t(a, s)
            }
            var o = +(new Date),
                u;
            t(a)
        }
        e({
            animate: r,
            requestAnimationFrame: t,
            easeOut: n
        })
    });
    provide("util/datetime", function(e) {
        using("util/util", function(t) {
            function h(e) {
                return e < 10 ? "0" + e : e
            }
            function p(e) {
                function i(e, n) {
                    return t && t[e] && (e = t[e]), e.replace(/%\{([\w_]+)\}/g, function(e, t) {
                        return n[t] !== undefined ? n[t] : e
                    })
                }
                var t = e && e.phrases,
                    n = e && e.months || s,
                    r = e && e.formats || o;
                this.timeAgo = function(e) {
                    var t = p.parseDate(e),
                        s = +(new Date),
                        o = s - t,
                        h;
                    return t ? isNaN(o) || o < u * 2 ? i("now") : o < a ? (h = Math.floor(o / u), i(r.abbr, {
                        number: h,
                        symbol: i(c, {
                            abbr: i("s"),
                            expanded: h > 1 ? i("seconds") : i("second")
                        })
                    })) : o < f ? (h = Math.floor(o / a), i(r.abbr, {
                        number: h,
                        symbol: i(c, {
                            abbr: i("m"),
                            expanded: h > 1 ? i("minutes") : i("minute")
                        })
                    })) : o < l ? (h = Math.floor(o / f), i(r.abbr, {
                        number: h,
                        symbol: i(c, {
                            abbr: i("h"),
                            expanded: h > 1 ? i("hours") : i("hour")
                        })
                    })) : o < l * 365 ? i(r.shortdate, {
                        day: t.getDate(),
                        month: i(n[t.getMonth()])
                    }) : i(r.longdate, {
                        day: t.getDate(),
                        month: i(n[t.getMonth()]),
                        year: t.getFullYear().toString().slice(2)
                    }) : ""
                }, this.localTimeStamp = function(e) {
                    var t = p.parseDate(e),
                        s = t && t.getHours();
                    return t ? i(r.full, {
                        day: t.getDate(),
                        month: i(n[t.getMonth()]),
                        year: t.getFullYear(),
                        hours24: h(s),
                        hours12: s < 13 ? s ? s : "12" : s - 12,
                        minutes: h(t.getMinutes()),
                        seconds: h(t.getSeconds()),
                        amPm: s < 12 ? i("AM") : i("PM")
                    }) : ""
                }
            }
            var n = /(\d{4})-?(\d{2})-?(\d{2})T(\d{2}):?(\d{2}):?(\d{2})(Z|[\+\-]\d{2}:?\d{2})/,
                r = /[a-z]{3,4} ([a-z]{3}) (\d{1,2}) (\d{1,2}):(\d{2}):(\d{2}) ([\+\-]\d{2}:?\d{2}) (\d{4})/i,
                i = /^\d+$/,
                s = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"],
                o = {
                    abbr: "%{number}%{symbol}",
                    shortdate: "%{day} %{month}",
                    longdate: "%{day} %{month} %{year}",
                    full: "%{hours12}:%{minutes} %{amPm} - %{day} %{month} %{year}"
                },
                u = 1e3,
                a = u * 60,
                f = a * 60,
                l = f * 24,
                c = '<abbr title="%{expanded}">%{abbr}</abbr>';
            p.parseDate = function(e) {
                var o = e || "",
                    u = o.toString(),
                    a,
                    f;
                return a = function() {
                    var e;
                    if (i.test(u))
                        return parseInt(u, 10);
                    if (e = u.match(r))
                        return Date.UTC(e[7], t.indexOf(s, e[1]), e[2], e[3], e[4], e[5]);
                    if (e = u.match(n))
                        return Date.UTC(e[1], e[2] - 1, e[3], e[4], e[5], e[6])
                }(), a ? (f = new Date(a), !isNaN(f.getTime()) && f) : !1
            }, e(p)
        })
    });
    provide("sandbox/frame", function(e) {
        using("sandbox/baseframe", "sandbox/minimal", "util/env", "util/promise", "util/util", function(t, n, r, i, s) {
            function h() {
                var e,
                    t;
                a = {};
                if (f)
                    return;
                e = document.body.offsetHeight, t = document.body.offsetWidth;
                if (e == c && t == l)
                    return;
                s.forEach(u, function(e) {
                    e.dispatchFrameResize(l, c)
                }), c = e, l = t
            }
            function p(e) {
                var t;
                return e.id ? e.id : (t = e.getAttribute("data-twttr-id")) ? t : (t = "twttr-sandbox-" + o++, e.setAttribute("data-twttr-id", t), t)
            }
            function d(e, t) {
                n.apply(this, [e, t]), this._resizeHandlers = [], u.push(this), this._win.addEventListener ? this._win.addEventListener("resize", s.bind(function() {
                    this.dispatchFrameResize()
                }, this), !0) : this._win.attachEvent("onresize", s.bind(function() {
                    this.dispatchFrameResize(this._win.event)
                }, this))
            }
            var o = 0,
                u = [],
                a = {},
                f,
                l = 0,
                c = 0;
            window.addEventListener ? window.addEventListener("resize", h, !0) : document.body.attachEvent("onresize", function() {
                h(window.event)
            }), d.prototype = new n, s.aug(d.prototype, {
                dispatchFrameResize: function() {
                    var e = this._frame.parentNode,
                        t = p(e),
                        n = a[t];
                    f = !0;
                    if (!this._resizeHandlers.length)
                        return;
                    n || (n = a[t] = {
                        w: this._frame.offsetWidth,
                        h: this._frame.offsetHeight
                    });
                    if (this._frameWidth == n.w && this._frameHeight == n.h)
                        return;
                    this._frameWidth = n.w, this._frameHeight = n.h, s.forEach(this._resizeHandlers, function(e) {
                        e(n.w, n.h)
                    }), window.setTimeout(function() {
                        a = {}
                    }, 50)
                },
                appendStyleSheet: function(e) {
                    var t = this._doc.createElement("link");
                    return t.type = "text/css", t.rel = "stylesheet", t.href = e, this.layout(s.bind(function() {
                        return this._head.appendChild(t)
                    }, this))
                },
                appendCss: function(e) {
                    var t;
                    return r.cspEnabled() ? i.reject("CSP enabled; cannot embed inline styles.") : (t = this._doc.createElement("style"), t.type = "text/css", t.styleSheet ? t.styleSheet.cssText = e : t.appendChild(this._doc.createTextNode(e)), this.layout(s.bind(function() {
                        return this._head.appendChild(t)
                    }, this)))
                },
                style: function(e) {
                    return this.layout(s.bind(function() {
                        s.forIn(e, s.bind(function(e, t) {
                            this._frame.style[e] = t
                        }, this))
                    }, this))
                },
                onresize: function(e) {
                    this._resizeHandlers.push(e)
                },
                width: function(e) {
                    return e !== undefined && (this._frame.style.width = e + "px"), r.ios() ? Math.min(this._frame.parentNode.offsetWidth, this._frame.offsetWidth) : this._frame.offsetWidth
                },
                height: function(e) {
                    return e !== undefined && (this._frame.height = e), this._frame.offsetHeight
                }
            }), d.createSandbox = function(e, n, r, i) {
                var s = new t(e, n, r, i);
                return s.ready().then(function(e) {
                    return new d(e.frame, e.layout)
                })
            }, e(d)
        })
    });
    provide("tfw/util/assets", function(e) {
        using("util/env", function(t) {
            function r(e, r) {
                var i = n[e],
                    s;
                return t.retina() ? s = "2x" : t.ie6() || t.ie7() ? s = "gif" : s = "default", r && (s += ".rtl"), i[s]
            }
            var n = {
                "embed/timeline.css": {
                    "default": "embed/timeline.6a72a50e1a93dc4d97ff897124263ab7.default.css",
                    "2x": "embed/timeline.6a72a50e1a93dc4d97ff897124263ab7.2x.css",
                    gif: "embed/timeline.6a72a50e1a93dc4d97ff897124263ab7.gif.css",
                    "default.rtl": "embed/timeline.6a72a50e1a93dc4d97ff897124263ab7.default.rtl.css",
                    "2x.rtl": "embed/timeline.6a72a50e1a93dc4d97ff897124263ab7.2x.rtl.css",
                    "gif.rtl": "embed/timeline.6a72a50e1a93dc4d97ff897124263ab7.gif.rtl.css"
                }
            };
            e(r)
        })
    });
    provide("util/layout", function(e) {
        using("util/promise", "util/logger", function(t, n) {
            function s() {}
            var r = [],
                i;
            s.prototype.enqueue = function(e, n) {
                return new t(function(t) {
                    r.push({
                        action: e,
                        resolver: t,
                        note: n
                    })
                })
            }, s.prototype.exec = function() {
                var e = r,
                    t;
                if (!e.length)
                    return;
                r = [];
                while (e.length)
                    t = e.shift(), t && t.action ? t.resolver.fulfill(t.action()) : t.resolver.reject()
            }, s.prototype.delayedExec = function() {
                i && window.clearTimeout(i), i = window.setTimeout(this.exec, 100)
            }, e(s)
        })
    });
    provide("tfw/widget/base", function(e) {
        using("dom/get", "util/domready", "util/iframe", "util/layout", "util/promise", "util/querystring", "util/typevalidator", "util/util", "tfw/util/globals", function(t, n, r, i, s, o, u, a, f) {
            function g(e) {
                var t;
                if (!e)
                    return;
                e.ownerDocument ? (this.srcEl = e, this.classAttr = e.className.split(" ")) : (this.srcOb = e, this.classAttr = []), t = this.params(), this.id = this.generateId(), this.setLanguage(), this.related = t.related || this.dataAttr("related"), this.partner = t.partner || this.dataAttr("partner") || f.val("partner"), this.dnt = t.dnt || this.dataAttr("dnt") || f.dnt() || "", this.styleAttr = [], this.targetEl = e.targetEl, this.completePromise = new s(a.bind(function(e) {
                    this.completeResolver = e
                }, this)), this.completed().then(function(e) {
                    if (!e || e == document.body)
                        return;
                    twttr.events.trigger("rendered", {
                        target: e
                    })
                })
            }
            function y() {
                a.forEach(p, function(e) {
                    e()
                }), g.doLayout()
            }
            function b(e) {
                if (!e)
                    return;
                return e.lang ? e.lang : b(e.parentNode)
            }
            var l = 0,
                c,
                h = {
                    list: [],
                    byId: {}
                },
                p = [],
                d = new i,
                v = "data-twttr-rendered",
                m = {
                    ar: {
                        "%{followers_count} followers": "عدد المتابعين %{followers_count}",
                        "100K+": "+100 ألف",
                        "10k unit": "10 آلاف وحدة",
                        Follow: "تابِع",
                        "Follow %{screen_name}": "تابِع %{screen_name}",
                        K: "ألف",
                        M: "م",
                        Tweet: "غرِّد",
                        "Tweet %{hashtag}": "غرِّد %{hashtag}",
                        "Tweet to %{name}": "غرِّد لـ %{name}"
                    },
                    da: {
                        "%{followers_count} followers": "%{followers_count} følgere",
                        "10k unit": "10k enhed",
                        Follow: "Følg",
                        "Follow %{screen_name}": "Følg %{screen_name}",
                        "Tweet to %{name}": "Tweet til %{name}"
                    },
                    de: {
                        "%{followers_count} followers": "%{followers_count} Follower",
                        "100K+": "100Tsd+",
                        "10k unit": "10tsd-Einheit",
                        Follow: "Folgen",
                        "Follow %{screen_name}": "%{screen_name} folgen",
                        K: "Tsd",
                        Tweet: "Twittern",
                        "Tweet to %{name}": "Tweet an %{name}"
                    },
                    es: {
                        "%{followers_count} followers": "%{followers_count} seguidores",
                        "10k unit": "10k unidad",
                        Follow: "Seguir",
                        "Follow %{screen_name}": "Seguir a %{screen_name}",
                        Tweet: "Twittear",
                        "Tweet %{hashtag}": "Twittear %{hashtag}",
                        "Tweet to %{name}": "Twittear a %{name}"
                    },
                    fa: {
                        "%{followers_count} followers": "%{followers_count} دنبال‌کننده",
                        "100K+": ">۱۰۰هزار",
                        "10k unit": "۱۰هزار واحد",
                        Follow: "دنبال کردن",
                        "Follow %{screen_name}": "دنبال کردن %{screen_name}",
                        K: "هزار",
                        M: "میلیون",
                        Tweet: "توییت",
                        "Tweet %{hashtag}": "توییت کردن %{hashtag}",
                        "Tweet to %{name}": "به %{name} توییت کنید"
                    },
                    fi: {
                        "%{followers_count} followers": "%{followers_count} seuraajaa",
                        "100K+": "100 000+",
                        "10k unit": "10 000 yksikköä",
                        Follow: "Seuraa",
                        "Follow %{screen_name}": "Seuraa käyttäjää %{screen_name}",
                        K: "tuhatta",
                        M: "milj.",
                        Tweet: "Twiittaa",
                        "Tweet %{hashtag}": "Twiittaa %{hashtag}",
                        "Tweet to %{name}": "Twiittaa käyttäjälle %{name}"
                    },
                    fil: {
                        "%{followers_count} followers": "%{followers_count} mga tagasunod",
                        "10k unit": "10k yunit",
                        Follow: "Sundan",
                        "Follow %{screen_name}": "Sundan si %{screen_name}",
                        Tweet: "I-tweet",
                        "Tweet %{hashtag}": "I-tweet ang %{hashtag}",
                        "Tweet to %{name}": "Mag-Tweet kay %{name}"
                    },
                    fr: {
                        "%{followers_count} followers": "%{followers_count} abonnés",
                        "10k unit": "unité de 10k",
                        Follow: "Suivre",
                        "Follow %{screen_name}": "Suivre %{screen_name}",
                        Tweet: "Tweeter",
                        "Tweet %{hashtag}": "Tweeter %{hashtag}",
                        "Tweet to %{name}": "Tweeter à %{name}"
                    },
                    he: {
                        "%{followers_count} followers": "%{followers_count} עוקבים",
                        "100K+": "מאות אלפים",
                        "10k unit": "עשרות אלפים",
                        Follow: "מעקב",
                        "Follow %{screen_name}": "לעקוב אחר %{screen_name}",
                        K: "אלף",
                        M: "מיליון",
                        Tweet: "ציוץ",
                        "Tweet %{hashtag}": "צייצו %{hashtag}",
                        "Tweet to %{name}": "ציוץ אל %{name}"
                    },
                    hi: {
                        "%{followers_count} followers": "%{followers_count} फ़ॉलोअर्स",
                        "100K+": "1 लाख+",
                        "10k unit": "10 हजार इकाईयां",
                        Follow: "फ़ॉलो",
                        "Follow %{screen_name}": "%{screen_name} को फ़ॉलो करें",
                        K: "हजार",
                        M: "मिलियन",
                        Tweet: "ट्वीट",
                        "Tweet %{hashtag}": "ट्वीट %{hashtag}",
                        "Tweet to %{name}": "%{name} को ट्वीट करें"
                    },
                    hu: {
                        "%{followers_count} followers": "%{followers_count} követő",
                        "100K+": "100E+",
                        "10k unit": "10E+",
                        Follow: "Követés",
                        "Follow %{screen_name}": "%{screen_name} követése",
                        K: "E",
                        "Tweet %{hashtag}": "%{hashtag} tweetelése",
                        "Tweet to %{name}": "Tweet küldése neki: %{name}"
                    },
                    id: {
                        "%{followers_count} followers": "%{followers_count} pengikut",
                        "100K+": "100 ribu+",
                        "10k unit": "10 ribu unit",
                        Follow: "Ikuti",
                        "Follow %{screen_name}": "Ikuti %{screen_name}",
                        K: "&nbsp;ribu",
                        M: "&nbsp;juta",
                        "Tweet to %{name}": "Tweet ke %{name}"
                    },
                    it: {
                        "%{followers_count} followers": "%{followers_count} follower",
                        "10k unit": "10k unità",
                        Follow: "Segui",
                        "Follow %{screen_name}": "Segui %{screen_name}",
                        "Tweet %{hashtag}": "Twitta %{hashtag}",
                        "Tweet to %{name}": "Twitta a %{name}"
                    },
                    ja: {
                        "%{followers_count} followers": "%{followers_count}人のフォロワー",
                        "100K+": "100K以上",
                        "10k unit": "万",
                        Follow: "フォローする",
                        "Follow %{screen_name}": "%{screen_name}さんをフォロー",
                        Tweet: "ツイート",
                        "Tweet %{hashtag}": "%{hashtag} をツイートする",
                        "Tweet to %{name}": "%{name}さんへツイートする"
                    },
                    ko: {
                        "%{followers_count} followers": "%{followers_count}명의 팔로워",
                        "100K+": "100만 이상",
                        "10k unit": "만 단위",
                        Follow: "팔로우",
                        "Follow %{screen_name}": "%{screen_name} 님 팔로우하기",
                        K: "천",
                        M: "백만",
                        Tweet: "트윗",
                        "Tweet %{hashtag}": "%{hashtag} 관련 트윗하기",
                        "Tweet to %{name}": "%{name} 님에게 트윗하기"
                    },
                    msa: {
                        "%{followers_count} followers": "%{followers_count} pengikut",
                        "100K+": "100 ribu+",
                        "10k unit": "10 ribu unit",
                        Follow: "Ikut",
                        "Follow %{screen_name}": "Ikut %{screen_name}",
                        K: "ribu",
                        M: "juta",
                        "Tweet to %{name}": "Tweet kepada %{name}"
                    },
                    nl: {
                        "%{followers_count} followers": "%{followers_count} volgers",
                        "100K+": "100k+",
                        "10k unit": "10k-eenheid",
                        Follow: "Volgen",
                        "Follow %{screen_name}": "%{screen_name} volgen",
                        K: "k",
                        M: " mln.",
                        Tweet: "Tweeten",
                        "Tweet %{hashtag}": "%{hashtag} tweeten",
                        "Tweet to %{name}": "Tweeten naar %{name}"
                    },
                    no: {
                        "%{followers_count} followers": "%{followers_count} følgere",
                        "100K+": "100 K+",
                        "10k unit": "10-K-enhet",
                        Follow: "Følg",
                        "Follow %{screen_name}": "Følg %{screen_name}",
                        "Tweet to %{name}": "Send en tweet til %{name}"
                    },
                    pl: {
                        "%{followers_count} followers": "%{followers_count} obserwujących",
                        "100K+": "100 tys.+",
                        "10k unit": "10 tys.",
                        Follow: "Obserwuj",
                        "Follow %{screen_name}": "Obserwuj %{screen_name}",
                        K: "tys.",
                        M: "mln",
                        Tweet: "Tweetnij",
                        "Tweet %{hashtag}": "Tweetnij %{hashtag}",
                        "Tweet to %{name}": "Tweetnij do %{name}"
                    },
                    pt: {
                        "%{followers_count} followers": "%{followers_count} seguidores",
                        "100K+": "+100 mil",
                        "10k unit": "10 mil unidades",
                        Follow: "Seguir",
                        "Follow %{screen_name}": "Seguir %{screen_name}",
                        K: "Mil",
                        Tweet: "Tweetar",
                        "Tweet %{hashtag}": "Tweetar %{hashtag}",
                        "Tweet to %{name}": "Tweetar para %{name}"
                    },
                    ru: {
                        "%{followers_count} followers": "Читатели: %{followers_count} ",
                        "100K+": "100 тыс.+",
                        "10k unit": "блок 10k",
                        Follow: "Читать",
                        "Follow %{screen_name}": "Читать %{screen_name}",
                        K: "тыс.",
                        M: "млн.",
                        Tweet: "Твитнуть",
                        "Tweet %{hashtag}": "Твитнуть %{hashtag}",
                        "Tweet to %{name}": "Твитнуть %{name}"
                    },
                    sv: {
                        "%{followers_count} followers": "%{followers_count} följare",
                        "10k unit": "10k",
                        Follow: "Följ",
                        "Follow %{screen_name}": "Följ %{screen_name}",
                        Tweet: "Tweeta",
                        "Tweet %{hashtag}": "Tweeta %{hashtag}",
                        "Tweet to %{name}": "Tweeta till %{name}"
                    },
                    th: {
                        "%{followers_count} followers": "%{followers_count} ผู้ติดตาม",
                        "100K+": "100พัน+",
                        "10k unit": "หน่วย 10พัน",
                        Follow: "ติดตาม",
                        "Follow %{screen_name}": "ติดตาม %{screen_name}",
                        M: "ล้าน",
                        Tweet: "ทวีต",
                        "Tweet %{hashtag}": "ทวีต %{hashtag}",
                        "Tweet to %{name}": "ทวีตถึง %{name}"
                    },
                    tr: {
                        "%{followers_count} followers": "%{followers_count} takipçi",
                        "100K+": "+100 bin",
                        "10k unit": "10 bin birim",
                        Follow: "Takip et",
                        "Follow %{screen_name}": "Takip et: %{screen_name}",
                        K: "bin",
                        M: "milyon",
                        Tweet: "Tweetle",
                        "Tweet %{hashtag}": "Tweetle: %{hashtag}",
                        "Tweet to %{name}": "Tweetle: %{name}"
                    },
                    ur: {
                        "%{followers_count} followers": "%{followers_count} فالورز",
                        "100K+": "ایک لاکھ سے زیادہ",
                        "10k unit": "دس ہزار یونٹ",
                        Follow: "فالو کریں",
                        "Follow %{screen_name}": "%{screen_name} کو فالو کریں",
                        K: "ہزار",
                        M: "ملین",
                        Tweet: "ٹویٹ کریں",
                        "Tweet %{hashtag}": "%{hashtag} ٹویٹ کریں",
                        "Tweet to %{name}": "%{name} کو ٹویٹ کریں"
                    },
                    "zh-cn": {
                        "%{followers_count} followers": "%{followers_count} 关注者",
                        "100K+": "10万+",
                        "10k unit": "1万单元",
                        Follow: "关注",
                        "Follow %{screen_name}": "关注 %{screen_name}",
                        K: "千",
                        M: "百万",
                        Tweet: "发推",
                        "Tweet %{hashtag}": "以 %{hashtag} 发推",
                        "Tweet to %{name}": "发推给 %{name}"
                    },
                    "zh-tw": {
                        "%{followers_count} followers": "%{followers_count} 位跟隨者",
                        "100K+": "超過十萬",
                        "10k unit": "1萬 單位",
                        Follow: "跟隨",
                        "Follow %{screen_name}": "跟隨 %{screen_name}",
                        K: "千",
                        M: "百萬",
                        Tweet: "推文",
                        "Tweet %{hashtag}": "推文%{hashtag}",
                        "Tweet to %{name}": "推文給%{name}"
                    }
                };
            a.aug(g.prototype, {
                setLanguage: function(e) {
                    var t;
                    e || (e = this.params().lang || this.dataAttr("lang") || b(this.srcEl)), e = e && e.toLowerCase();
                    if (!e)
                        return this.lang = "en";
                    if (m[e])
                        return this.lang = e;
                    t = e.replace(/[\-_].*/, "");
                    if (m[t])
                        return this.lang = t;
                    this.lang = "en"
                },
                _: function(e, t) {
                    var n = this.lang;
                    t = t || {};
                    if (!n || !m.hasOwnProperty(n))
                        n = this.lang = "en";
                    return e = m[n] && m[n][e] || e, this.ringo(e, t, /%\{([\w_]+)\}/g)
                },
                ringo: function(e, t, n) {
                    return n = n || /\{\{([\w_]+)\}\}/g, e.replace(n, function(e, n) {
                        return t[n] !== undefined ? t[n] : e
                    })
                },
                add: function(e) {
                    h.list.push(this), h.byId[this.id] = e
                },
                create: function(e, t, n) {
                    var i = this,
                        o;
                    return n[v] = !0, o = r(a.aug({
                        id: this.id,
                        src: e,
                        "class": this.classAttr.join(" ")
                    }, n), t, this.targetEl && this.targetEl.ownerDocument), this.srcEl ? this.layout(function() {
                        return i.srcEl.parentNode.replaceChild(o, i.srcEl), i.completeResolver.fulfill(o), o
                    }) : this.targetEl ? this.layout(function() {
                        return i.targetEl.appendChild(o), i.completeResolver.fulfill(o), o
                    }) : s.reject("Did not append widget")
                },
                params: function() {
                    var e,
                        t;
                    return this.srcOb ? t = this.srcOb : (e = this.srcEl && this.srcEl.href && this.srcEl.href.split("?")[1], t = e ? o.decode(e) : {}), this.params = function() {
                        return t
                    }, t
                },
                dataAttr: function(e) {
                    return this.srcEl && this.srcEl.getAttribute("data-" + e)
                },
                attr: function(e) {
                    return this.srcEl && this.srcEl.getAttribute(e)
                },
                layout: function(e) {
                    return d.enqueue(e)
                },
                styles: {
                    base: [["font", "normal normal normal 11px/18px 'Helvetica Neue', Arial, sans-serif"], ["margin", "0"], ["padding", "0"], ["whiteSpace", "nowrap"]],
                    button: [["fontWeight", "bold"], ["textShadow", "0 1px 0 rgba(255,255,255,.5)"]],
                    large: [["fontSize", "13px"], ["lineHeight", "26px"]],
                    vbubble: [["fontSize", "16px"]]
                },
                width: function() {
                    throw new Error(name + " not implemented")
                },
                height: function() {
                    return this.size == "m" ? 20 : 28
                },
                minWidth: function() {},
                maxWidth: function() {},
                minHeight: function() {},
                maxHeight: function() {},
                dimensions: function() {
                    function e(e) {
                        switch (typeof e) {
                        case "string":
                            return e;
                        case "undefined":
                            return;
                        default:
                            return e + "px"
                        }
                    }
                    var t = {
                        width: this.width(),
                        height: this.height()
                    };
                    return this.minWidth() && (t["min-width"] = this.minWidth()), this.maxWidth() && (t["max-width"] = this.maxWidth()), this.minHeight() && (t["min-height"] = this.minHeight()), this.maxHeight() && (t["max-height"] = this.maxHeight()), a.forIn(t, function(n, r) {
                        t[n] = e(r)
                    }), t
                },
                generateId: function() {
                    return this.srcEl && this.srcEl.id || "twitter-widget-" + l++
                },
                completed: function() {
                    return this.completePromise
                }
            }), g.afterLoad = function(e) {
                p.push(e)
            }, g.doLayout = function() {
                d.exec()
            }, g.doLayoutAsync = function() {
                d.delayedExec()
            }, g.init = function(e) {
                c = e
            }, g.find = function(e) {
                return e && h.byId[e] ? h.byId[e].element : null
            }, g.embed = function(e) {
                var n = c.widgets,
                    r = [],
                    i = [];
                u.isArray(e) || (e = [e || document]), a.forEach(e, function(e) {
                    a.forIn(n, function(n, i) {
                        var s,
                            o;
                        n.match(/\./) ? (s = n.split("."), o = t.all(s[1], e, s[0])) : o = e.getElementsByTagName(n), a.forEach(o, function(e) {
                            if (e.getAttribute(v))
                                return;
                            e.setAttribute(v, "true"), r.push(new i(e))
                        })
                    })
                }), g.doLayout(), a.forEach(r, function(e) {
                    h.byId[e.id] = e, h.list.push(e), i.push(e.completed()), e.render(c)
                }), s.every.apply(null, i).then(function(e) {
                    e = a.filter(e, function(t) {
                        return t
                    });
                    if (!e.length)
                        return;
                    twttr.events.trigger("loaded", {
                        widgets: e
                    })
                }), g.doLayoutAsync(), y()
            }, window.setInterval(function() {
                g.doLayout()
            }, 500), e(g)
        })
    });
    provide("tfw/widget/intent", function(e) {
        using("tfw/widget/base", "util/util", "util/querystring", "util/uri", "util/promise", function(t, n, r, i, s) {
            function p(e) {
                var t = Math.round(c / 2 - a / 2),
                    n = 0;
                l > f && (n = Math.round(l / 2 - f / 2)), window.open(e, undefined, [u, "width=" + a, "height=" + f, "left=" + t, "top=" + n].join(","))
            }
            function d(e, t) {
                using("tfw/hub/client", function(n) {
                    n.openIntent(e, t)
                })
            }
            function v(e) {
                var t = ~location.host.indexOf("poptip.com") ? "https://poptip.com" : location.href,
                    n = "original_referer=" + t;
                return [e, n].join(e.indexOf("?") == -1 ? "?" : "&")
            }
            function m(e) {
                var t,
                    r,
                    i,
                    s;
                e = e || window.event, t = e.target || e.srcElement;
                if (e.altKey || e.metaKey || e.shiftKey)
                    return;
                while (t) {
                    if (~n.indexOf(["A", "AREA"], t.nodeName))
                        break;
                    t = t.parentNode
                }
                t && t.href && (r = t.href.match(o), r && (s = v(t.href), s = s.replace(/^http[:]/, "https:"), s = s.replace(/^\/\//, "https://"), g(s, t), e.returnValue = !1, e.preventDefault && e.preventDefault()))
            }
            function g(e, t) {
                if (twttr.events.hub && t) {
                    var n = new y(h.generateId(), t);
                    h.add(n), d(e, t), twttr.events.trigger("click", {
                        target: t,
                        region: "intent",
                        type: "click",
                        data: {}
                    })
                } else
                    p(e)
            }
            function y(e, t) {
                this.id = e, this.element = this.srcEl = t
            }
            function b(e) {
                this.srcEl = [], this.element = e
            }
            var o = /twitter\.com(\:\d{2,4})?\/intent\/(\w+)/,
                u = "scrollbars=yes,resizable=yes,toolbar=no,location=yes",
                a = 550,
                f = 520,
                l = screen.height,
                c = screen.width,
                h;
            b.prototype = new t, n.aug(b.prototype, {
                render: function(e) {
                    return h = this, window.__twitterIntentHandler || (document.addEventListener ? document.addEventListener("click", m, !1) : document.attachEvent && document.attachEvent("onclick", m), window.__twitterIntentHandler = !0), s.fulfill(document.body)
                }
            }), b.open = g, e(b)
        })
    });
    provide("tfw/widget/syndicatedbase", function(e) {
        using("tfw/widget/base", "tfw/widget/intent", "tfw/util/assets", "tfw/util/globals", "tfw/util/tracking", "dom/classname", "dom/get", "dom/delegate", "sandbox/frame", "util/env", "util/promise", "util/twitter", "util/typevalidator", "util/util", function(t, n, r, i, s, o, u, a, f, l, c, h, p, d) {
            function C() {
                b = k.VALID_COLOR.test(i.val("widgets:link-color")) && RegExp.$1, E = k.VALID_COLOR.test(i.val("widgets:border-color")) && RegExp.$1, w = i.val("widgets:theme")
            }
            function k(e) {
                if (!e)
                    return;
                var n;
                this.readyPromise = new c(d.bind(function(e) {
                    this.readyResolver = e
                }, this)), this.renderedPromise = new c(d.bind(function(e) {
                    this.renderResolver = e
                }, this)), t.apply(this, [e]), n = this.params(), this.targetEl = this.srcEl && this.srcEl.parentNode || n.targetEl || document.body, this.predefinedWidth = k.VALID_UNIT.test(n.width || this.attr("width")) && RegExp.$1, this.layout(d.bind(function() {
                    return this.containerWidth = this.targetEl && this.targetEl.offsetWidth
                }, this)).then(d.bind(function(e) {
                    var t = this.predefinedWidth || e || this.dimensions.DEFAULT_WIDTH;
                    this.height = k.VALID_UNIT.test(n.height || this.attr("height")) && RegExp.$1, this.width = Math.max(this.dimensions.MIN_WIDTH, Math.min(t, this.dimensions.DEFAULT_WIDTH))
                }, this)), k.VALID_COLOR.test(n.linkColor || this.dataAttr("link-color")) ? this.linkColor = RegExp.$1 : this.linkColor = b, k.VALID_COLOR.test(n.borderColor || this.dataAttr("border-color")) ? this.borderColor = RegExp.$1 : this.borderColor = E, this.theme = n.theme || this.attr("data-theme") || w, this.theme = /(dark|light)/.test(this.theme) ? this.theme : "", this.classAttr.push(l.touch() ? "is-touch" : "not-touch"), l.ie9() && this.classAttr.push("ie9"), f.createSandbox({
                    "class": this.renderedClassNames,
                    id: this.id
                }, {
                    width: "1px",
                    height: "0px",
                    border: "none",
                    position: "absolute",
                    visibility: "hidden"
                }, d.bind(function(e) {
                    this.srcEl ? this.targetEl.insertBefore(e, this.srcEl) : this.targetEl.appendChild(e)
                }, this), this.layout).then(d.bind(function(e) {
                    this.setupSandbox(e)
                }, this))
            }
            function L(e, t) {
                return e + t
            }
            function A(e, t) {
                return e == 2 || e == 3 && t == 0
            }
            var v = [".customisable", ".customisable:link", ".customisable:visited", ".customisable:hover", ".customisable:focus", ".customisable:active", ".customisable-highlight:hover", ".customisable-highlight:focus", "a:hover .customisable-highlight", "a:focus .customisable-highlight"],
                m = ["a:hover .ic-mask", "a:focus .ic-mask"],
                g = [".customisable-border"],
                y = [".timeline-header h1.summary", ".timeline-header h1.summary a:link", ".timeline-header h1.summary a:visited"],
                b,
                w,
                E,
                S = {
                    TWEET: 0,
                    RETWEET: 10
                },
                x = 6,
                T = 8 / 9,
                N = 16 / 9;
            k.prototype = new t, d.aug(k.prototype, {
                setupSandbox: function(e) {
                    this.sandbox = e, c.some(e.appendCss("body{display:none}"), e.setBaseTarget("_blank"), e.appendStyleSheet(twttr.widgets.config.assetUrl() + "/" + r("embed/timeline.css"))).then(d.bind(function() {
                        this.readyResolver.fulfill(e)
                    }, this))
                },
                ready: function() {
                    return this.readyPromise
                },
                rendered: function() {
                    return this.renderedPromise
                },
                contentWidth: function(e) {
                    var t = this.dimensions,
                        n = this.fullBleedPhoto ? 0 : this.chromeless && this.narrow ? t.NARROW_MEDIA_PADDING_CL : this.chromeless ? t.WIDE_MEDIA_PADDING_CL : this.narrow ? t.NARROW_MEDIA_PADDING : t.WIDE_MEDIA_PADDING;
                    return (e || this.width) - n
                },
                addSiteStyles: function() {
                    var e = d.bind(function(e) {
                            return (this.theme == "dark" ? ".thm-dark " : "") + e
                        }, this),
                        t = [];
                    this.headingStyle && t.push(d.map(y, e).join(",") + "{" + this.headingStyle + "}"), this.linkColor && (t.push(d.map(v, e).join(",") + "{color:" + this.linkColor + "}"), t.push(d.map(m, e).join(",") + "{background-color:" + this.linkColor + "}")), this.borderColor && t.push(d.map(g, e).concat(this.theme == "dark" ? [".thm-dark.customisable-border"] : []).join(",") + "{border-color:" + this.borderColor + "}");
                    if (!t.length)
                        return;
                    return this.sandbox.appendCss(t.join(""))
                },
                setNarrow: function() {
                    var e = this.narrow;
                    return this.narrow = this.width < this.dimensions.NARROW_WIDTH, e != this.narrow ? this.layout(d.bind(function() {
                        return o.toggle(this.element, "var-narrow", this.narrow)
                    }, this)) : c.fulfill(this.narrow)
                },
                bindIntentHandlers: function() {
                    function r(n) {
                        var r = u.ancestor(".tweet", this, t),
                            i = d.aug({}, e.baseScribeData(), e.extractTweetScribeDetails(r));
                        s.scribeInteraction(n, i, !0, e.dnt)
                    }
                    var e = this,
                        t = this.element;
                    a.delegate(t, "click", "A", r), a.delegate(t, "click", "BUTTON", r), a.delegate(t, "click", ".profile", function() {
                        e.addUrlParams(this)
                    }), a.delegate(t, "click", ".follow-button", function(t) {
                        var r;
                        if (t.altKey || t.metaKey || t.shiftKey)
                            return;
                        if (l.ios() || l.android())
                            return;
                        if (p.asBoolean(this.getAttribute("data-age-gate")))
                            return;
                        r = h.intentForProfileURL(this.href), r && (n.open(r, e.sandbox.element()), a.preventDefault(t))
                    }), a.delegate(t, "click", ".web-intent", function(t) {
                        e.addUrlParams(this);
                        if (t.altKey || t.metaKey || t.shiftKey)
                            return;
                        n.open(this.href, e.sandbox.element()), a.preventDefault(t)
                    })
                },
                baseScribeData: function() {
                    return {}
                },
                extractTweetScribeDetails: function(e) {
                    var t,
                        n,
                        r = {};
                    return e ? (t = e.getAttribute("data-tweet-id"), n = e.getAttribute("data-rendered-tweet-id") || t, n == t ? r[n] = {
                        item_type: S.TWEET
                    } : t && (r[n] = {
                        item_type: S.RETWEET,
                        target_type: S.TWEET,
                        target_id: t
                    }), r) : r
                },
                constrainMedia: function(e, t) {
                    var n = 0,
                        r = this.fullBleedPhoto ? 600 : 375,
                        i = u.one("multi-photo", e, "DIV"),
                        s = i && +i.getAttribute("data-photo-count");
                    e = e || this.element, t = t || this.contentWidth();
                    if (!e)
                        return;
                    return d.forEach(u.all("autosized-media", e), d.bind(function(e) {
                        var i = k.scaleDimensions(e.getAttribute("data-width"), e.getAttribute("data-height"), t, r);
                        this.layout(function() {
                            e.width = i.width, e.height = i.height
                        }), n = i.height > n ? i.height : n
                    }, this)), d.forEach(u.all("cropped-media", e, "IMG"), d.bind(function(e) {
                        var i = t - 12,
                            o = e.parentNode,
                            u = e.getAttribute("data-crop-x") || 0,
                            a = e.getAttribute("data-crop-y") || 0,
                            f,
                            l,
                            c = A(s, e.getAttribute("data-image-index")),
                            h = Math.floor(i / 2 - x),
                            p = Math.floor(h / (c ? T : N)),
                            d;
                        c || (p -= x / 2), d = k.scaleDimensions(e.getAttribute("data-width"), e.getAttribute("data-height"), h, r, h, p), f = d.width - h - u, l = d.height - p - a, f < 0 && Math.max(0, u += f), l < 0 && Math.max(0, a += l), this.layout(function() {
                            e.width = d.width, e.height = d.height, o.style.width = h - 1 + "px", o.style.height = p + "px", u && (e.style.marginLeft = "-" + Math.floor(d.width * u / 100) + "px"), a && (e.style.marginTop = "-" + Math.floor(d.height * a / 100) + "px")
                        }), n = d.height * (c ? 2 : 1) > n ? d.height : n
                    }, this)), n
                },
                collapseRegions: function() {
                    d.forEach(u.all("collapsible-container", this.element), d.bind(function(e) {
                        var t = e.children,
                            n = t.length && e.offsetWidth,
                            r = t.length && d.map(t, function(e) {
                                return e.offsetWidth
                            }),
                            i = t.length,
                            s,
                            u;
                        if (!t.length)
                            return;
                        while (i > 0) {
                            i--, s = d.reduce(r, L, 0);
                            if (!n || !s)
                                return;
                            if (s < n)
                                return;
                            u = t[i].getAttribute("data-collapsed-class");
                            if (!u)
                                continue;
                            o.add(this.element, u), r[i] = t[i].offsetWidth
                        }
                    }, this))
                }
            }), k.VALID_UNIT = /^([0-9]+)( ?px)?$/, k.VALID_COLOR = /^(#(?:[0-9a-f]{3}|[0-9a-f]{6}))$/i, k.retinize = function(e) {
                if (!l.retina())
                    return;
                d.forEach(e.getElementsByTagName("IMG"), function(e) {
                    var t = e.getAttribute("data-src-2x");
                    t && (e.src = t)
                })
            }, k.scaleDimensions = function(e, t, n, r, i, s) {
                return n = n || e, r = r || t, i = i || 0, s = s || 0, e > n && (t *= n / e, e = n), t > r && (e *= r / t, t = r), e < i && (t *= i / e, e = i), t < s && (e *= s / t, t = s), {
                    width: Math.floor(e),
                    height: Math.floor(t)
                }
            }, C(), e(k)
        })
    });
    provide("tfw/widget/timeline", function(e) {
        using("tfw/widget/base", "tfw/widget/syndicatedbase", "util/datetime", "util/promise", "anim/transition", "tfw/util/article", "tfw/util/data", "tfw/util/tracking", "tfw/util/params", "util/css", "util/env", "util/throttle", "util/twitter", "util/querystring", "util/typevalidator", "util/util", "dom/delegate", "dom/classname", "dom/get", function(t, n, r, i, s, o, u, a, f, l, c, h, p, d, v, m, g, y, b) {
            function I(e) {
                if (!e)
                    return;
                var t,
                    r,
                    i,
                    s,
                    o,
                    u,
                    a,
                    f;
                n.apply(this, [e]), t = this.params(), r = (t.chrome || this.dataAttr("chrome") || "").split(" "), this.preview = t.previewParams, this.widgetId = t.widgetId || this.dataAttr("widget-id"), this.instanceId = ++F, this.cursors = {
                    maxPosition: 0,
                    minPosition: 0
                }, (s = t.screenName || this.dataAttr("screen-name")) || (o = t.userId || this.dataAttr("user-id")) ? this.override = {
                    overrideType: "user",
                    overrideId: o,
                    overrideName: s,
                    withReplies: v.asBoolean(t.showReplies || this.dataAttr("show-replies")) ? "true" : "false"
                } : (s = t.favoritesScreenName || this.dataAttr("favorites-screen-name")) || (o = t.favoritesUserId || this.dataAttr("favorites-user-id")) ? this.override = {
                    overrideType: "favorites",
                    overrideId: o,
                    overrideName: s
                } : ((s = t.listOwnerScreenName || this.dataAttr("list-owner-screen-name")) || (o = t.listOwnerId || this.dataAttr("list-owner-id"))) && ((u = t.listId || this.dataAttr("list-id")) || (a = t.listSlug || this.dataAttr("list-slug"))) ? this.override = {
                    overrideType: "list",
                    overrideOwnerId: o,
                    overrideOwnerName: s,
                    overrideId: u,
                    overrideName: a
                } : (f = t.customTimelineId || this.dataAttr("custom-timeline-id")) ? this.override = {
                    overrideType: "custom",
                    overrideId: f
                } : this.override = {}, this.tweetLimit = v.asInt(t.tweetLimit || this.dataAttr("tweet-limit")), this.staticTimeline = this.tweetLimit > 0, r.length && (i = ~m.indexOf(r, "none"), this.chromeless = i || ~m.indexOf(r, "transparent"), this.headerless = i || ~m.indexOf(r, "noheader"), this.footerless = i || ~m.indexOf(r, "nofooter"), this.borderless = i || ~m.indexOf(r, "noborders"), this.noscrollbar = ~m.indexOf(r, "noscrollbar")), this.headingStyle = l.sanitize(t.headingStyle || this.dataAttr("heading-style"), undefined, !0), this.classAttr.push("twitter-timeline-rendered"), this.ariaPolite = t.ariaPolite || this.dataAttr("aria-polite")
            }
            var w = "1.0",
                E = {
                    CLIENT_SIDE_USER: 0,
                    CLIENT_SIDE_APP: 2
                },
                S = "timeline",
                x = "new-tweets-bar",
                T = "timeline-header",
                N = "timeline-footer",
                C = "stream",
                k = "h-feed",
                L = "tweet",
                A = "expanded",
                O = "detail-expander",
                M = "expand",
                _ = "permalink",
                D = "twitter-follow-button",
                P = "no-more-pane",
                H = "pending-scroll-in",
                B = "pending-new-tweet",
                j = "pending-new-tweet-display",
                F = 0;
            I.prototype = new n, m.aug(I.prototype, {
                renderedClassNames: "twitter-timeline twitter-timeline-rendered",
                dimensions: {
                    DEFAULT_HEIGHT: "600",
                    DEFAULT_WIDTH: "520",
                    NARROW_WIDTH: "320",
                    MIN_WIDTH: "180",
                    MIN_HEIGHT: "200",
                    WIDE_MEDIA_PADDING: 81,
                    NARROW_MEDIA_PADDING: 16,
                    WIDE_MEDIA_PADDING_CL: 60,
                    NARROW_MEDIA_PADDING_CL: 12
                },
                create: function(e) {
                    var r = this.sandbox.createElement("div"),
                        i,
                        s,
                        o,
                        u = [],
                        f;
                    r.innerHTML = e.body, i = r.children[0] || !1;
                    if (!i)
                        return;
                    return this.reconfigure(e.config), this.discardStaticOverflow(i), this.sandbox.setTitle(i.getAttribute("data-iframe-title") || "Timeline"), n.retinize(i), this.constrainMedia(i), this.searchQuery = i.getAttribute("data-search-query"), this.profileId = i.getAttribute("data-profile-id"), this.timelineType = i.getAttribute("data-timeline-type"), f = this.getTweetDetails(r), m.forIn(f, function(e) {
                        u.push(e)
                    }), o = this.baseScribeData(), o.item_ids = u, o.item_details = f, this.timelineType && a.enqueue({
                        page: this.timelineType + "_timeline",
                        component: "timeline",
                        element: "initial",
                        action: u.length ? "results" : "no_results"
                    }, o, !0, this.dnt), a.enqueue({
                        page: "timeline",
                        component: "timeline",
                        element: "initial",
                        action: u.length ? "results" : "no_results"
                    }, o, !0, this.dnt), a.flush(), this.ariaPolite == "assertive" && (s = b.one(x, i, "DIV"), s.setAttribute("aria-polite", "assertive")), i.id = this.id, i.className += " " + this.classAttr.join(" "), i.lang = this.lang, this.augmentWidgets(i), this.ready().then(m.bind(function(e) {
                        e.appendChild(i).then(m.bind(function() {
                            this.renderResolver.fulfill(this.sandbox)
                        }, this)), e.style({
                            cssText: "",
                            border: "none",
                            maxWidth: "100%",
                            minWidth: this.dimensions.MIN_WIDTH + "px"
                        }), this.layout(m.bind(function() {
                            this.srcEl && this.srcEl.parentNode && this.srcEl.parentNode.removeChild(this.srcEl), this.predefinedWidth = this.width, this.predefinedHeight = this.height, this.width = e.width(this.width), this.height = e.height(this.height)
                        }, this)).then(m.bind(function() {
                            this.completeResolver.fulfill(this.sandbox.element()), this.width < this.predefinedWidth && (this.layout(m.bind(function() {
                                this.width = e.width(this.predefinedWidth)
                            }, this)), t.doLayoutAsync()), this.height < this.predefinedHeight && (this.layout(m.bind(function() {
                                this.height = e.height(this.predefinedHeight), this.recalculateStreamHeight()
                            }, this)), t.doLayoutAsync())
                        }, this)), this.setNarrow().then(m.bind(function() {
                            this.sandbox.onresize(m.bind(this.handleResize, this))
                        }, this))
                    }, this)), i
                },
                render: function(e, n) {
                    return !this.preview && !this.widgetId ? (this.completeResolver.reject(400), this.completed()) : (this.staticTimeline ? this.rendered().then(m.bind(function(e) {
                        this.layout(m.bind(function() {
                            e.height(this.height = this.element.offsetHeight)
                        }, this)), t.doLayoutAsync()
                    }, this)) : this.rendered().then(m.bind(function() {
                        this.recalculateStreamHeight(), t.doLayoutAsync()
                    }, this)), this.preview ? this.getPreviewTimeline() : this.getTimeline(), n && this.completed().then(n), this.completed())
                },
                getPreviewTimeline: function() {
                    u.timelinePreview({
                        success: m.bind(function(e) {
                            this.ready().then(m.bind(function() {
                                this.element = this.create(e), this.readTranslations(), this.bindInteractions(), this.updateCursors(e.headers, {
                                    initial: !0
                                }), t.doLayoutAsync()
                            }, this))
                        }, this),
                        error: function(e) {
                            if (!e || !e.headers) {
                                this.completeResolver.fulfill(this.srcEl);
                                return
                            }
                            this.completeResolver.reject(e.headers.status)
                        },
                        params: this.preview
                    })
                },
                getTimeline: function() {
                    a.initPostLogging(), u.timeline(m.aug({
                        id: this.widgetId,
                        instanceId: this.instanceId,
                        dnt: this.dnt,
                        lang: this.lang,
                        success: m.bind(function(e) {
                            this.ready().then(m.bind(function() {
                                this.element = this.create(e), this.readTranslations(), this.bindInteractions(), this.updateTimeStamps(), this.updateCursors(e.headers, {
                                    initial: !0
                                }), e.headers.xPolling && /\d/.test(e.headers.xPolling) && (this.pollInterval = e.headers.xPolling * 1e3), this.staticTimeline || this.schedulePolling(), t.doLayoutAsync()
                            }, this))
                        }, this),
                        error: function(e) {
                            if (!e || !e.headers) {
                                this.completeResolver.fulfill(this.srcEl);
                                return
                            }
                            this.completeResolver.reject(e.headers.status)
                        }
                    }, this.override))
                },
                reconfigure: function(e) {
                    this.lang = e.lang, this.theme || (this.theme = e.theme), this.theme == "dark" && this.classAttr.push("thm-dark"), this.chromeless && this.classAttr.push("var-chromeless"), this.borderless && this.classAttr.push("var-borderless"), this.headerless && this.classAttr.push("var-headerless"), this.footerless && this.classAttr.push("var-footerless"), this.staticTimeline && this.classAttr.push("var-static"), !this.linkColor && e.linkColor && n.VALID_COLOR.test(e.linkColor) && (this.linkColor = RegExp.$1), !this.height && n.VALID_UNIT.test(e.height) && (this.height = RegExp.$1), this.height = Math.max(this.dimensions.MIN_HEIGHT, this.height ? this.height : this.dimensions.DEFAULT_HEIGHT), this.preview && this.classAttr.push("var-preview"), this.narrow = this.width <= this.dimensions.NARROW_WIDTH, this.narrow && this.classAttr.push("var-narrow"), this.addSiteStyles()
                },
                getTweetDetails: function(e) {
                    var t = b.one(k, e),
                        n,
                        r = {},
                        i,
                        s,
                        o = 0;
                    n = t && t.children || [];
                    for (; i = n[o]; o++)
                        s = b.one(_, i, "A"), m.aug(r, this.extractTweetScribeDetails(i));
                    return r
                },
                baseScribeData: function() {
                    return {
                        widget_id: this.widgetId,
                        widget_origin: o.url(),
                        client_version: w,
                        message: this.partner,
                        query: this.searchQuery,
                        profile_id: this.profileId
                    }
                },
                bindInteractions: function() {
                    var e = this,
                        t = this.element,
                        n = !0;
                    this.bindIntentHandlers(), g.delegate(t, "click", ".load-tweets", function(t) {
                        n && (n = !1, e.forceLoad(), g.stop(t))
                    }), g.delegate(t, "click", ".display-sensitive-image", function(n) {
                        e.showNSFW(b.ancestor("." + L, this, t)), g.stop(n)
                    }), g.delegate(t, "mouseover", "." + S, function() {
                        e.mouseOver = !0
                    }), g.delegate(t, "mouseout", "." + S, function() {
                        e.mouseOver = !1
                    }), g.delegate(t, "mouseover", "." + x, function() {
                        e.mouseOverNotifier = !0
                    }), g.delegate(t, "mouseout", "." + x, function() {
                        e.mouseOverNotifier = !1, window.setTimeout(function() {
                            e.hideNewTweetNotifier()
                        }, 3e3)
                    });
                    if (this.staticTimeline)
                        return;
                    g.delegate(t, "click", "." + M, function(n) {
                        if (n.altKey || n.metaKey || n.shiftKey)
                            return;
                        e.toggleExpando(b.ancestor("." + L, this, t)), g.stop(n)
                    }), g.delegate(t, "click", "A", function(e) {
                        g.stopPropagation(e)
                    }), g.delegate(t, "click", ".with-expansion", function(t) {
                        e.toggleExpando(this), g.stop(t)
                    }), g.delegate(t, "click", ".load-more", function() {
                        e.loadMore()
                    }), g.delegate(t, "click", "." + x, function() {
                        e.scrollToTop(), e.hideNewTweetNotifier(!0)
                    })
                },
                scrollToTop: function() {
                    var e = b.one(C, this.element, "DIV");
                    e.scrollTop = 0, e.focus()
                },
                update: function() {
                    var e = this,
                        t = b.one(k, this.element),
                        n = t && t.children[0],
                        r = n && n.getAttribute("data-tweet-id");
                    this.updateTimeStamps(), this.requestTweets(r, !0, function(t) {
                        t.childNodes.length > 0 && e.insertNewTweets(t)
                    })
                },
                loadMore: function() {
                    var e = this,
                        t = b.all(L, this.element, "LI").pop(),
                        n = t && t.getAttribute("data-tweet-id");
                    this.requestTweets(n, !1, function(t) {
                        var r = b.one(P, e.element, "P"),
                            i = t.childNodes[0];
                        r.style.cssText = "", i && i.getAttribute("data-tweet-id") == n && t.removeChild(i);
                        if (t.childNodes.length > 0) {
                            e.appendTweets(t);
                            return
                        }
                        y.add(e.element, "no-more"), r.focus()
                    })
                },
                forceLoad: function() {
                    var e = this,
                        t = !!b.all(k, this.element, "OL").length;
                    this.requestTweets(1, !0, function(n) {
                        n.childNodes.length && (e[t ? "insertNewTweets" : "appendTweets"](n), y.add(e.element, "has-tweets"))
                    })
                },
                schedulePolling: function(e) {
                    var t = this;
                    if (this.pollInterval === null)
                        return;
                    e = twttr.widgets.poll || e || this.pollInterval || 1e4, e > -1 && window.setTimeout(function() {
                        this.isUpdating || t.update(), t.schedulePolling()
                    }, e)
                },
                updateCursors: function(e, t) {
                    (t || {}).initial ? (this.cursors.maxPosition = e.maxPosition, this.cursors.minPosition = e.minPosition) : (t || {}).newer ? this.cursors.maxPosition = e.maxPosition || this.cursors.maxPosition : this.cursors.minPosition = e.minPosition || this.cursors.minPosition
                },
                requestTweets: function(e, t, r) {
                    var i = this,
                        s = {
                            id: this.widgetId,
                            instanceId: this.instanceId,
                            screenName: this.widgetScreenName,
                            userId: this.widgetUserId,
                            withReplies: this.widgetShowReplies,
                            dnt: this.dnt,
                            lang: this.lang
                        };
                    t && this.cursors.maxPosition ? s.minPosition = this.cursors.maxPosition : !t && this.cursors.minPosition ? s.maxPosition = this.cursors.minPosition : t ? s.sinceId = e : s.maxId = e, s.complete = function() {
                        this.isUpdating = !1
                    }, s.error = function(e) {
                        if (e && e.headers) {
                            if (e.headers.status == "404") {
                                i.pollInterval = null;
                                return
                            }
                            if (e.headers.status == "503") {
                                i.pollInterval *= 1.5;
                                return
                            }
                        }
                    }, s.success = function(e) {
                        var s = i.sandbox.createDocumentFragment(),
                            o = i.sandbox.createElement("div"),
                            u,
                            f = [],
                            l,
                            c;
                        i.updateCursors(e.headers, {
                            newer: t
                        }), e && e.headers && e.headers.xPolling && /\d+/.test(e.headers.xPolling) && (i.pollInterval = e.headers.xPolling * 1e3);
                        if (e && e.body !== undefined) {
                            o.innerHTML = e.body;
                            if (o.children[0] && o.children[0].tagName != "LI")
                                return;
                            l = i.getTweetDetails(o);
                            for (c in l)
                                l.hasOwnProperty(c) && f.push(c);
                            f.length && (u = i.baseScribeData(), u.item_ids = f, u.item_details = l, u.event_initiator = t ? E.CLIENT_SIDE_APP : E.CLIENT_SIDE_USER, this.timelineType && a.enqueue({
                                page: this.timelineType + "_timeline",
                                component: "timeline",
                                element: "initial",
                                action: f.length ? "results" : "no_results"
                            }, u, !0, this.dnt), a.enqueue({
                                page: "timeline",
                                component: "timeline",
                                element: t ? "newer" : "older",
                                action: "results"
                            }, u, !0, i.dnt), a.flush()), n.retinize(o), i.constrainMedia(o);
                            while (o.children[0])
                                s.appendChild(o.children[0]);
                            r(s)
                        }
                    }, u.timelinePoll(m.aug(s, this.override))
                },
                insertNewTweets: function(e) {
                    var t = this,
                        n = b.one(C, this.element, "DIV"),
                        r = b.one(k, n, "OL"),
                        i = r.offsetHeight,
                        o;
                    r.insertBefore(e, r.firstChild), o = r.offsetHeight - i;
                    if (n.scrollTop > 40 || this.mouseIsOver()) {
                        n.scrollTop = n.scrollTop + o, this.updateTimeStamps(), this.showNewTweetNotifier();
                        return
                    }
                    y.remove(this.element, H), r.style.cssText = "margin-top: -" + o + "px", window.setTimeout(function() {
                        n.scrollTop = 0, y.add(t.element, H), c.cssTransitions() ? r.style.cssText = "" : s.animate(function(e) {
                            e < o ? r.style.cssText = "margin-top: -" + (o - e) + "px" : r.style.cssText = ""
                        }, o, 500, s.easeOut)
                    }, 500), this.updateTimeStamps(), this.timelineType != "custom" && this.gcTweets(50)
                },
                appendTweets: function(e) {
                    var t = b.one(C, this.element, "DIV"),
                        n = b.one(k, t, "OL");
                    n.appendChild(e), this.updateTimeStamps()
                },
                gcTweets: function(e) {
                    var t = b.one(k, this.element, "OL"),
                        n = t.children.length,
                        r;
                    e = e || 50;
                    for (; n > e && (r = t.children[n - 1]); n--)
                        t.removeChild(r)
                },
                showNewTweetNotifier: function() {
                    var e = this,
                        t = b.one(x, this.element, "DIV"),
                        n = t.children[0];
                    t.style.cssText = "", t.removeChild(n), t.appendChild(n), y.add(this.element, j), window.setTimeout(function() {
                        y.add(e.element, B)
                    }, 10), this.newNoticeDisplayTime = +(new Date), window.setTimeout(function() {
                        e.hideNewTweetNotifier()
                    }, 5e3)
                },
                hideNewTweetNotifier: function(e) {
                    var t = this;
                    if (!e && this.mouseOverNotifier)
                        return;
                    y.remove(this.element, B), window.setTimeout(function() {
                        y.remove(t.element, j)
                    }, 500)
                },
                augmentWidgets: function(e) {
                    var t = b.one(D, e, "A");
                    if (!t)
                        return;
                    t.setAttribute("data-related", this.related), t.setAttribute("data-partner", this.partner), t.setAttribute("data-dnt", this.dnt), t.setAttribute("data-search-query", this.searchQuery), t.setAttribute("data-profile-id", this.profileId), this.width < 250 && t.setAttribute("data-show-screen-name", "false"), twttr.widgets.load(t.parentNode)
                },
                discardStaticOverflow: function(e) {
                    var t = b.one(k, e, "OL"),
                        n;
                    if (this.staticTimeline) {
                        this.height = 0;
                        while (n = t.children[this.tweetLimit])
                            t.removeChild(n)
                    }
                },
                hideStreamScrollBar: function() {
                    var e = b.one(C, this.element, "DIV"),
                        t = b.one(k, this.element, "OL"),
                        n;
                    e.style.width = "", n = this.element.offsetWidth - t.offsetWidth, n > 0 && (e.style.width = this.element.offsetWidth + n + "px")
                },
                readTranslations: function() {
                    var e = this.element,
                        t = "data-dt-";
                    this.datetime = new r(m.compact({
                        phrases: {
                            now: e.getAttribute(t + "now"),
                            s: e.getAttribute(t + "s"),
                            m: e.getAttribute(t + "m"),
                            h: e.getAttribute(t + "h"),
                            second: e.getAttribute(t + "second"),
                            seconds: e.getAttribute(t + "seconds"),
                            minute: e.getAttribute(t + "minute"),
                            minutes: e.getAttribute(t + "minutes"),
                            hour: e.getAttribute(t + "hour"),
                            hours: e.getAttribute(t + "hours")
                        },
                        months: e.getAttribute(t + "months").split("|"),
                        formats: {
                            abbr: e.getAttribute(t + "abbr"),
                            shortdate: e.getAttribute(t + "short"),
                            longdate: e.getAttribute(t + "long")
                        }
                    }))
                },
                updateTimeStamps: function() {
                    var e = b.all(_, this.element, "A"),
                        t,
                        n,
                        r = 0,
                        i,
                        s;
                    for (; t = e[r]; r++) {
                        i = t.getAttribute("data-datetime"), s = i && this.datetime.timeAgo(i, this.i18n), n = t.getElementsByTagName("TIME")[0];
                        if (!s)
                            continue;
                        if (n && n.innerHTML) {
                            n.innerHTML = s;
                            continue
                        }
                        t.innerHTML = s
                    }
                },
                mouseIsOver: function() {
                    return this.mouseOver
                },
                addUrlParams: function(e) {
                    var t = this,
                        n = {
                            tw_w: this.widgetId,
                            related: this.related,
                            partner: this.partner,
                            query: this.searchQuery,
                            profile_id: this.profileId,
                            original_referer: o.url(),
                            tw_p: "embeddedtimeline"
                        };
                    return this.addUrlParams = f(n, function(e) {
                        var n = b.ancestor("." + L, e, t.element);
                        return n && {
                                tw_i: n.getAttribute("data-tweet-id")
                            }
                    }), this.addUrlParams(e)
                },
                showNSFW: function(e) {
                    var t = b.one("nsfw", e, "DIV"),
                        r,
                        i,
                        s = 0,
                        o,
                        u,
                        a,
                        f;
                    if (!t)
                        return;
                    i = n.scaleDimensions(t.getAttribute("data-width"), t.getAttribute("data-height"), this.contentWidth(), t.getAttribute("data-height")), r = !!(u = t.getAttribute("data-player")), r ? a = this.sandbox.createElement("iframe") : (a = this.sandbox.createElement("img"), u = t.getAttribute(c.retina() ? "data-image-2x" : "data-image"), a.alt = t.getAttribute("data-alt"), f = this.sandbox.createElement("a"), f.href = t.getAttribute("data-href"), f.appendChild(a)), a.title = t.getAttribute("data-title"), a.src = u, a.width = i.width, a.height = i.height, o = b.ancestor("." + O, t, e), s = i.height - t.offsetHeight, t.parentNode.replaceChild(r ? a : f, t), o.style.cssText = "height:" + (o.offsetHeight + s) + "px"
                },
                toggleExpando: function(e) {
                    var r = b.one(O, e, "DIV"),
                        i = r && r.children[0],
                        s = i && i.getAttribute("data-expanded-media"),
                        o,
                        u = 0,
                        a = b.one(M, e, "A"),
                        f = a && a.getElementsByTagName("B")[0],
                        l = f && (f.innerText || f.textContent),
                        c;
                    if (!f)
                        return;
                    this.layout(function() {
                        f.innerHTML = a.getAttribute("data-toggled-text"), a.setAttribute("data-toggled-text", l)
                    });
                    if (y.present(e, A)) {
                        this.layout(function() {
                            y.remove(e, A)
                        });
                        if (!r) {
                            t.doLayout();
                            return
                        }
                        this.layout(function() {
                            r.style.cssText = "", i.innerHTML = ""
                        }), t.doLayout();
                        return
                    }
                    s && (o = this.sandbox.createElement("DIV"), o.innerHTML = s, n.retinize(o), u = this.constrainMedia(o), this.layout(function() {
                        i.appendChild(o)
                    })), r && this.layout(function() {
                        c = Math.max(i.offsetHeight, u), r.style.cssText = "height:" + c + "px"
                    }), this.layout(function() {
                        y.add(e, A)
                    }), t.doLayout()
                },
                recalculateStreamHeight: function(e) {
                    var t = b.one(T, this.element, "DIV"),
                        n = b.one(N, this.element, "DIV"),
                        r = b.one(C, this.element, "DIV");
                    this.layout(m.bind(function() {
                        var i = t.offsetHeight + (n ? n.offsetHeight : 0),
                            s = e || this.sandbox.height();
                        r.style.cssText = "height:" + (s - i - 2) + "px", this.noscrollbar && this.hideStreamScrollBar()
                    }, this))
                },
                handleResize: function(e, n) {
                    var r = Math.min(this.dimensions.DEFAULT_WIDTH, Math.max(this.dimensions.MIN_WIDTH, Math.min(this.predefinedWidth || this.dimensions.DEFAULT_WIDTH, e)));
                    if (r == this.width && n == this.height)
                        return;
                    this.width = r, this.height = n, this.setNarrow(), this.constrainMedia(this.element, this.contentWidth(r)), this.staticTimeline ? this.layout(m.bind(function() {
                        this.height = this.element.offsetHeight, this.sandbox.height(this.height)
                    }, this)) : this.recalculateStreamHeight(n), t.doLayoutAsync()
                }
            }), e(I)
        })
    });
    provide("tfw/widget/embed", function(e) {
        using("tfw/widget/base", "tfw/widget/syndicatedbase", "util/datetime", "tfw/util/params", "dom/classname", "dom/get", "util/env", "util/promise", "util/util", "util/throttle", "util/twitter", "tfw/util/article", "tfw/util/data", "tfw/util/tracking", function(t, n, r, i, s, o, u, a, f, l, c, h, p, d) {
            function w(e, t, n, r) {
                var i = o.one("subject", e, "BLOCKQUOTE"),
                    s = o.one("reply", e, "BLOCKQUOTE"),
                    u = i && i.getAttribute("data-tweet-id"),
                    a = s && s.getAttribute("data-tweet-id"),
                    l = {},
                    c = {};
                if (!u)
                    return;
                l[u] = {
                    item_type: 0
                }, d.enqueue({
                    page: "tweet",
                    section: "subject",
                    component: "tweet",
                    action: "results"
                }, f.aug({}, t, {
                    item_ids: [u],
                    item_details: l
                }), !0, r);
                if (!a)
                    return;
                c[a] = {
                    item_type: 0
                }, d.enqueue({
                    page: "tweet",
                    section: "conversation",
                    component: "tweet",
                    action: "results"
                }, f.aug({}, t, {
                    item_ids: [a],
                    item_details: c,
                    associations: {
                        4: {
                            association_id: u,
                            association_type: 4
                        }
                    }
                }), !0, r)
            }
            function E(e, t, n) {
                var r = {};
                if (!e)
                    return;
                r[e] = {
                    item_type: 0
                }, d.enqueue({
                    page: "tweet",
                    section: "subject",
                    component: "rawembedcode",
                    action: "no_results"
                }, {
                    client_version: v,
                    widget_origin: h.url(),
                    widget_frame: h.frameUrl(),
                    message: t,
                    item_ids: [e],
                    item_details: r
                }, !0, n)
            }
            function S(e, t, n, r) {
                g[e] = g[e] || [], g[e].push({
                    s: n,
                    f: r,
                    lang: t
                })
            }
            function x() {
                b.length && twttr.widgets.load(b)
            }
            function T(e) {
                if (!e)
                    return;
                var t,
                    r,
                    i;
                n.apply(this, [e]), t = this.params(), r = this.srcEl && this.srcEl.getElementsByTagName("A"), i = r && r[r.length - 1], this.hideThread = (t.conversation || this.dataAttr("conversation")) == "none" || ~f.indexOf(this.classAttr, "tw-hide-thread"), this.hideCard = (t.cards || this.dataAttr("cards")) == "hidden" || ~f.indexOf(this.classAttr, "tw-hide-media");
                if ((t.align || this.attr("align")) == "left" || ~f.indexOf(this.classAttr, "tw-align-left"))
                    this.align = "left";
                else if ((t.align || this.attr("align")) == "right" || ~f.indexOf(this.classAttr, "tw-align-right"))
                    this.align = "right";
                else if ((t.align || this.attr("align")) == "center" || ~f.indexOf(this.classAttr, "tw-align-center"))
                    this.align = "center", this.containerWidth > this.dimensions.MIN_WIDTH * (1 / .7) && this.width > this.containerWidth * .7 && (this.width = this.containerWidth * .7);
                this.narrow = t.narrow || this.width <= this.dimensions.NARROW_WIDTH, this.narrow && this.classAttr.push("var-narrow"), this.tweetId = t.tweetId || i && c.status(i.href)
            }
            var v = "2.0",
                m = "tweetembed",
                g = {},
                y = [],
                b = [];
            T.prototype = new n, f.aug(T.prototype, {
                renderedClassNames: "twitter-tweet twitter-tweet-rendered",
                dimensions: {
                    DEFAULT_HEIGHT: "0",
                    DEFAULT_WIDTH: "500",
                    NARROW_WIDTH: "350",
                    MIN_WIDTH: "220",
                    MIN_HEIGHT: "0",
                    WIDE_MEDIA_PADDING: 32,
                    NARROW_MEDIA_PADDING: 32
                },
                create: function(e) {
                    var t = this.sandbox.createElement("div"),
                        r,
                        i;
                    t.innerHTML = e, r = t.children[0] || !1;
                    if (!r)
                        return;
                    return this.theme == "dark" && this.classAttr.push("thm-dark"), this.linkColor && this.addSiteStyles(), s.present(r, "media-forward") && (this.fullBleedPhoto = !0), this.augmentWidgets(r), n.retinize(r), r.id = this.id, r.className += " " + this.classAttr.join(" "), r.lang = this.lang, this.sandbox.setTitle(r.getAttribute("data-iframe-title") || "Tweet"), this.sandbox.appendChild(r).then(f.bind(function() {
                        this.renderResolver.fulfill(this.sandbox)
                    }, this)), this.sandbox.style({
                        cssText: "",
                        display: "block",
                        maxWidth: "99%",
                        minWidth: this.dimensions.MIN_WIDTH + "px",
                        padding: "0",
                        borderRadius: "5px",
                        margin: "10px 0",
                        border: "#ddd 1px solid",
                        borderTopColor: "#eee",
                        borderBottomColor: "#bbb",
                        boxShadow: "0 1px 3px rgba(0,0,0,0.15)",
                        position: "absolute",
                        visibility: "hidden"
                    }), i = this.layout(f.bind(function() {
                        this.predefinedWidth = this.width, this.width = this.sandbox.width(this.width), this.collapseRegions()
                    }, this), "Insert Sandbox"), i.then(f.bind(function() {
                        this.constrainMedia(r, this.contentWidth(this.width)), this.setNarrow().then(f.bind(function() {
                            this.layout(f.bind(function() {
                                this.completeResolver.fulfill(this.sandbox.element())
                            }, this))
                        }, this))
                    }, this)), w(r, this.baseScribeData(), this.partner, this.dnt), r
                },
                render: function(e, n) {
                    var r = "",
                        i = this.tweetId;
                    return i ? (this.hideCard && (r += "c"), this.hideThread && (r += "t"), r && (i += "-" + r), this.rendered().then(f.bind(function(e) {
                        this.srcEl && this.srcEl.parentNode && this.layout(f.bind(function() {
                            this.srcEl && this.srcEl.parentNode && this.srcEl.parentNode.removeChild(this.srcEl)
                        }, this), "Remove Embed Code"), this.align == "center" ? e.style({
                            margin: "7px auto",
                            cssFloat: "none"
                        }) : this.align && (this.width == this.dimensions.DEFAULT_WIDTH && (this.predefinedWidth = this.width = this.dimensions.NARROW_WIDTH), e.style({
                            cssFloat: this.align
                        })), this.layout(f.bind(function() {
                            this.height = this.sandbox.height(this.element.offsetHeight)
                        }, this)).then(f.bind(function() {
                            return t.doLayoutAsync(), this.layout(f.bind(function() {
                                this.height = this.sandbox.height(this.element.offsetHeight)
                            }, this))
                        }, this)).then(f.bind(function() {
                            e.onresize(f.bind(this.handleResize, this))
                        }, this)), e.style({
                            position: "static",
                            visibility: "visible"
                        }), t.doLayoutAsync()
                    }, this)), S(i, this.lang, f.bind(function(n) {
                        this.ready().then(f.bind(function() {
                            this.element = this.create(n), this.readTimestampTranslations(), this.updateTimeStamps(), this.bindIntentHandlers(), t.doLayoutAsync()
                        }, this))
                    }, this), f.bind(function() {
                        E(this.tweetId, this.partner, this.dnt), this.completeResolver.fulfill(this.srcEl)
                    }, this)), y.push(this.rendered()), n && this.completed().then(n), this.completed()) : (this.completeResolver.fulfill(this.srcEl), this.completed())
                },
                augmentWidgets: function(e) {
                    var t = o.one("twitter-follow-button", e, "A");
                    if (!t)
                        return;
                    t.setAttribute("data-related", this.related), t.setAttribute("data-partner", this.partner), t.setAttribute("data-dnt", this.dnt), t.setAttribute("data-show-screen-name", "false"), b.push(t.parentNode)
                },
                addUrlParams: function(e) {
                    var t = this,
                        n = {
                            related: this.related,
                            partner: this.partner,
                            original_referer: h.url(),
                            tw_p: m
                        };
                    return this.addUrlParams = i(n, function(e) {
                        var n = o.ancestor(".tweet", e, t.element);
                        return {
                            tw_i: n.getAttribute("data-tweet-id")
                        }
                    }), this.addUrlParams(e)
                },
                baseScribeData: function() {
                    return {
                        client_version: v,
                        widget_origin: h.url(),
                        widget_frame: h.frameUrl(),
                        message: this.partner
                    }
                },
                handleResize: function(e) {
                    var n = Math.min(this.dimensions.DEFAULT_WIDTH, Math.max(this.dimensions.MIN_WIDTH, Math.min(this.predefinedWidth || this.dimensions.DEFAULT_WIDTH, e)));
                    if (n == this.width)
                        return;
                    this.width = n, this.setNarrow(), this.constrainMedia(this.element, this.contentWidth(n)), this.collapseRegions(), this.layout(f.bind(function() {
                        this.height = this.element.offsetHeight, this.sandbox.height(this.height)
                    }, this), "Embed Resize"), t.doLayoutAsync()
                },
                readTimestampTranslations: function() {
                    var e = this.element,
                        t = "data-dt-",
                        n = e.getAttribute(t + "months") || "";
                    this.datetime = new r(f.compact({
                        phrases: {
                            AM: e.getAttribute(t + "am"),
                            PM: e.getAttribute(t + "pm")
                        },
                        months: n.split("|"),
                        formats: {
                            full: e.getAttribute(t + "full")
                        }
                    }))
                },
                updateTimeStamps: function() {
                    var e = o.one("long-permalink", this.element, "A"),
                        n = e.getAttribute("data-datetime"),
                        r = n && this.datetime.localTimeStamp(n),
                        i = e.getElementsByTagName("TIME")[0];
                    if (!r)
                        return;
                    this.layout(function() {
                        if (i && i.innerHTML) {
                            i.innerHTML = r;
                            return
                        }
                        e.innerHTML = r
                    }, "Update Timestamp"), t.doLayoutAsync()
                }
            }), T.fetchAndRender = function() {
                var e = g,
                    n = [],
                    r,
                    i;
                g = {};
                if (e.keys)
                    n = e.keys();
                else
                    for (r in e)
                        e.hasOwnProperty(r) && n.push(r);
                if (!n.length)
                    return;
                d.initPostLogging(), i = e[n[0]][0].lang, p.tweets({
                    ids: n.sort(),
                    lang: i,
                    complete: function(n) {
                        f.forIn(n, function(t, n) {
                            var r = e[t];
                            f.forEach(r, function(e) {
                                e.s && e.s.call(this, n)
                            }), delete e[t]
                        }), t.doLayout(), f.forIn(e, function(e, t) {
                            f.forEach(t, function(t) {
                                t.f && t.f.call(this, e)
                            })
                        }), t.doLayout()
                    }
                }), a.every.apply(null, y).then(function() {
                    x(), d.flush()
                })
            }, t.afterLoad(T.fetchAndRender), e(T)
        })
    });
    provide("dom/textsize", function(e) {
        function n(e, t, n) {
            var r = [],
                i = 0,
                s;
            for (; s = n[i]; i++)
                r.push(s[0]), r.push(s[1]);
            return e + t + r.join(":")
        }
        function r(e) {
            var t = e || "";
            return t.replace(/([A-Z])/g, function(e) {
                return "-" + e.toLowerCase()
            })
        }
        var t = {};
        e(function(e, i, s) {
            var o = document.createElement("span"),
                u = {},
                a = "",
                f,
                l = 0,
                c = 0,
                h = [];
            s = s || [], i = i || "", a = n(e, i, s);
            if (t[a])
                return t[a];
            o.className = i + " twitter-measurement";
            try {
                for (; f = s[l]; l++)
                    o.style[f[0]] = f[1]
            } catch (p) {
                for (; f = s[c]; c++)
                    h.push(r(f[0]) + ":" + f[1]);
                o.setAttribute("style", h.join(";") + ";")
            }
            return o.innerHTML = e, document.body.appendChild(o), u.width = o.clientWidth || o.offsetWidth, u.height = o.clientHeight || o.offsetHeight, document.body.removeChild(o), delete o, t[a] = u
        })
    });
    provide("tfw/widget/follow", function(e) {
        using("util/util", "tfw/widget/base", "util/querystring", "util/uri", "util/twitter", "util/promise", "dom/textsize", function(t, n, r, i, s, o, u) {
            function a(e) {
                if (!e)
                    return;
                var t,
                    r,
                    i,
                    o;
                n.apply(this, [e]), t = this.params(), r = t.size || this.dataAttr("size"), i = t.showScreenName || this.dataAttr("show-screen-name"), o = t.count || this.dataAttr("count"), this.classAttr.push("twitter-follow-button"), this.showScreenName = i != "false", this.showCount = t.showCount !== !1 && this.dataAttr("show-count") != "false", o == "none" && (this.showCount = !1), this.explicitWidth = t.width || this.dataAttr("width") || "", this.screenName = t.screen_name || t.screenName || s.screenName(this.attr("href")), this.preview = t.preview || this.dataAttr("preview") || "", this.align = t.align || this.dataAttr("align") || "", this.size = r == "large" ? "l" : "m"
            }
            a.prototype = new n, t.aug(a.prototype, {
                parameters: function() {
                    var e = {
                        screen_name: this.screenName,
                        lang: this.lang,
                        show_count: this.showCount,
                        show_screen_name: this.showScreenName,
                        align: this.align,
                        id: this.id,
                        preview: this.preview,
                        size: this.size,
                        partner: this.partner,
                        dnt: this.dnt,
                        _: +(new Date)
                    };
                    return t.compact(e), r.encode(e)
                },
                width: function() {
                    if (this.calculatedWidth)
                        return this.calculatedWidth;
                    if (this.explicitWidth)
                        return this.explicitWidth;
                    var e = {
                            cnt: 13,
                            btn: 24,
                            xlcnt: 22,
                            xlbtn: 38
                        },
                        n = this.showScreenName ? "Follow %{screen_name}" : "Follow",
                        r = this._(n, {
                            screen_name: "@" + this.screenName
                        }),
                        i = ~t.indexOf(["ja", "ko"], this.lang) ? this._("10k unit") : this._("M"),
                        s = this._("%{followers_count} followers", {
                            followers_count: "88888" + i
                        }),
                        o = 0,
                        a = 0,
                        f,
                        l,
                        c = this.styles.base;
                    return this.size == "l" ? (c = c.concat(this.styles.large), f = e.xlbtn, l = e.xlcnt) : (f = e.btn, l = e.cnt), this.showCount && (a = u(s, "", c).width + l), o = u(r, "", c.concat(this.styles.button)).width + f, this.calculatedWidth = o + a
                },
                render: function(e, n) {
                    if (!this.screenName)
                        return o.reject("Missing Screen Name").then(n);
                    var r = twttr.widgets.config.assetUrl() + "/widgets/follow_button.1401325387.html#" + this.parameters(),
                        i = this.create(r, this.dimensions(), {
                            title: this._("Twitter Follow Button")
                        }).then(t.bind(function(e) {
                            return this.element = e
                        }, this));
                    return n && i.then(n), i
                }
            }), e(a)
        })
    });
    provide("tfw/widget/tweetbutton", function(e) {
        using("tfw/widget/base", "tfw/util/globals", "util/util", "util/querystring", "util/uri", "util/twitter", "util/typevalidator", "dom/textsize", function(t, n, r, i, s, o, u, a) {
            function p(e) {
                t.apply(this, [e]);
                var i = this.params(),
                    u = i.count || this.dataAttr("count"),
                    a = i.size || this.dataAttr("size"),
                    p = s.getScreenNameFromPage(),
                    d = "" + (i.shareWithRetweet || this.dataAttr("share-with-retweet") || n.val("share-with-retweet"));
                this.classAttr.push("twitter-tweet-button"), i.type == "hashtag" || ~r.indexOf(this.classAttr, "twitter-hashtag-button") ? (this.type = "hashtag", this.classAttr.push("twitter-hashtag-button")) : i.type == "mention" || ~r.indexOf(this.classAttr, "twitter-mention-button") ? (this.type = "mention", this.classAttr.push("twitter-mention-button")) : this.classAttr.push("twitter-share-button"), this.text = i.text || this.dataAttr("text"), this.text && /\+/.test(this.text) && !/ /.test(this.text) && (this.text = this.text.replace(/\+/g, " ")), this.counturl = i.counturl || this.dataAttr("counturl"), this.searchlink = i.searchlink || this.dataAttr("searchlink"), this.button_hashtag = o.hashTag(i.button_hashtag || i.hashtag || this.dataAttr("button-hashtag"), !1), this.size = a == "large" ? "l" : "m", this.align = i.align || this.dataAttr("align") || "", this.via = i.via || this.dataAttr("via"), this.hashtags = i.hashtags || this.dataAttr("hashtags"), this.screen_name = o.screenName(i.screen_name || i.screenName || this.dataAttr("button-screen-name")), this.url = i.url || this.dataAttr("url"), this.type ? (this.count = "none", this.shareWithRetweet = "never", p && (this.related = this.related ? p + "," + this.related : p)) : (this.text = this.text || f, this.url = this.url || s.getCanonicalURL() || l, this.count = ~r.indexOf(c, u) ? u : "horizontal", this.count = this.count == "vertical" && this.size == "l" ? "none" : this.count, this.via = this.via || p, d && ~r.indexOf(h, d) && (this.shareWithRetweet = d.replace("-", "_")))
            }
            var f = document.title,
                l = encodeURI(location.href),
                c = ["vertical", "horizontal", "none"],
                h = [, "never", "publisher-first", "publisher-only", "author-first", "author-only"];
            p.prototype = new t, r.aug(p.prototype, {
                widgetUrlParams: function() {
                    return r.compact({
                        text: this.text,
                        url: this.url,
                        via: this.via,
                        related: this.related,
                        count: this.count,
                        lang: this.lang,
                        counturl: this.counturl,
                        searchlink: this.searchlink,
                        placeid: this.placeid,
                        original_referer: location.href,
                        id: this.id,
                        size: this.size,
                        type: this.type,
                        screen_name: this.screen_name,
                        share_with_retweet: this.shareWithRetweet,
                        button_hashtag: this.button_hashtag,
                        hashtags: this.hashtags,
                        align: this.align,
                        partner: this.partner,
                        dnt: this.dnt,
                        _: +(new Date)
                    })
                },
                parameters: function() {
                    return i.encode(this.widgetUrlParams())
                },
                height: function() {
                    return this.count == "vertical" ? 62 : this.size == "m" ? 20 : 28
                },
                width: function() {
                    var e = {
                            ver: 8,
                            cnt: 14,
                            btn: 24,
                            xlcnt: 18,
                            xlbtn: 38
                        },
                        t = this.count == "vertical",
                        n = this.type == "hashtag" && this.button_hashtag ? "Tweet %{hashtag}" : this.type == "mention" && this.screen_name ? "Tweet to %{name}" : "Tweet",
                        i = this._(n, {
                            name: "@" + this.screen_name,
                            hashtag: "#" + this.button_hashtag
                        }),
                        s = this._("K"),
                        o = this._("100K+"),
                        u = (t ? "8888" : "88888") + s,
                        f = 0,
                        l = 0,
                        c = 0,
                        h = 0,
                        p = this.styles.base,
                        d = p;
                    return ~r.indexOf(["ja", "ko"], this.lang) ? u += this._("10k unit") : u = u.length > o.length ? u : o, t ? (d = p.concat(this.styles.vbubble), h = e.ver, c = e.btn) : this.size == "l" ? (p = d = p.concat(this.styles.large), c = e.xlbtn, h = e.xlcnt) : (c = e.btn, h = e.cnt), this.count != "none" && (l = a(u, "", d).width + h), f = a(i, "", p.concat(this.styles.button)).width + c, t ? f > l ? f : l : this.calculatedWidth = f + l
                },
                render: function(e, t) {
                    var n = twttr.widgets.config.assetUrl() + "/widgets/tweet_button.1401325387.html#" + this.parameters(),
                        i;
                    return this.count && this.classAttr.push("twitter-count-" + this.count), i = this.create(n, this.dimensions(), {
                        title: this._("Twitter Tweet Button")
                    }).then(r.bind(function(e) {
                        return this.element = e
                    }, this)), t && i.then(t), i
                }
            }), e(p)
        })
    });
    provide("tfw/factories", function(e) {
        using("util/util", "util/promise", "util/twitter", "tfw/widget/base", "tfw/widget/tweetbutton", "tfw/widget/follow", "tfw/widget/embed", "tfw/widget/timeline", function(t, n, r, i, s, o, u, a) {
            function f(e, r, s, o) {
                return e = e || [], s = s || {}, function() {
                    var u,
                        a,
                        f,
                        l = Array.prototype.slice.apply(arguments, [0, e.length]),
                        c = Array.prototype.slice.apply(arguments, [e.length]),
                        h;
                    return t.forEach(c, function(e) {
                        if (!e)
                            return;
                        if (e.nodeType === 1) {
                            f = e;
                            return
                        }
                        if (t.isType("function", e)) {
                            u = e;
                            return
                        }
                        t.isType("object", e) && (a = e)
                    }), l.length != e.length || c.length === 0 ? (u && t.async(function() {
                        u(!1)
                    }), n.reject("Not enough parameters")) : f ? (a = t.aug(a || {}, s), a.targetEl = f, t.forEach(e, function(e) {
                        a[e] = l.shift()
                    }), h = new r(a), i.doLayout(), h.render(twttr.widgets.config), o && o(), u && h.completed().then(u, function() {
                        u(!1)
                    }), h.completed()) : (u && t.async(function() {
                        u(!1)
                    }), n.reject("No target specified"))
                }
            }
            function l(e) {
                var n;
                e.linkColor = e.linkColor || e.previewParams.link_color, e.theme = e.theme || e.previewParams.theme, e.height = e.height || e.previewParams.height, n = new a(e), this.render = t.bind(n.render, n), this.completed = t.bind(n.completed, n)
            }
            var c = f(["url"], s, {
                    type: "share"
                }),
                h = f(["hashtag"], s, {
                    type: "hashtag"
                }),
                p = f(["screenName"], s, {
                    type: "mention"
                }),
                d = f(["screenName"], o),
                v = f(["tweetId"], u, {}, u.fetchAndRender),
                m = f(["widgetId"], a),
                g = f(["previewParams"], l),
                y = {
                    createShareButton: c,
                    createMentionButton: p,
                    createHashtagButton: h,
                    createFollowButton: d,
                    createTweet: v,
                    createTweetEmbed: v,
                    createTimeline: m
                };
            r.isTwitterURL(window.location.href) && (y.createTimelinePreview = g), e(y)
        })
    });
    !function() {
        window.twttr = window.twttr || {}, twttr.host = twttr.host || "platform.twitter.com", using("util/domready", "util/env", function(e, t) {
            function n(e) {
                return (e || !/^http\:$/.test(window.location.protocol)) && !twttr.ignoreSSL ? "https" : "http"
            }
            if (t.ie6())
                return;
            if (twttr.widgets && twttr.widgets.loaded)
                return twttr.widgets.load(), !1;
            if (twttr.init)
                return !1;
            twttr.init = !0, twttr._e = twttr._e || [], twttr.ready = twttr.ready || function(e) {
                twttr.widgets && twttr.widgets.loaded ? e(twttr) : twttr._e.push(e)
            }, using.path.length || (using.path = n() + "://" + twttr.host + "/js"), twttr.ignoreSSL = twttr.ignoreSSL || !1;
            var r = [];
            twttr.events = {
                bind: function(e, t) {
                    return r.push([e, t])
                }
            }, e(function() {
                using("tfw/widget/base", "tfw/widget/follow", "tfw/widget/tweetbutton", "tfw/widget/embed", "tfw/widget/timeline", "tfw/widget/intent", "tfw/factories", "tfw/util/article", "util/events", "util/util", function(e, t, i, s, o, u, a, f, l, c) {
                    function v(e) {
                        var t = twttr.host;
                        return n(e) == "https" && twttr.secureHost && (t = twttr.secureHost), n(e) + "://" + t
                    }
                    function m() {
                        using("tfw/hub/client", function(e) {
                            twttr.events.hub = e.init(h), e.init(h, !0)
                        })
                    }
                    var h = {
                            widgets: {
                                "a.twitter-share-button": i,
                                "a.twitter-mention-button": i,
                                "a.twitter-hashtag-button": i,
                                "a.twitter-follow-button": t,
                                "blockquote.twitter-tweet": s,
                                "a.twitter-timeline": o,
                                "div.twitter-timeline": o,
                                body: u
                            }
                        },
                        p = twttr.events && twttr.events.hub ? twttr.events : {},
                        d;
                    h.assetUrl = v, twttr.widgets = twttr.widgets || {}, c.aug(twttr.widgets, a, {
                        config: {
                            assetUrl: v
                        },
                        load: function(t) {
                            e.init(h), e.embed(t), twttr.widgets.loaded = !0
                        }
                    }), c.aug(twttr.events, p, l.Emitter), d = twttr.events.bind, twttr.events.bind = function(e, t) {
                        m(), this.bind = d, this.bind(e, t)
                    }, c.forEach(r, function(e) {
                        twttr.events.bind(e[0], e[1])
                    }), c.forEach(twttr._e, function(e) {
                        c.async(function() {
                            e(twttr)
                        })
                    }), twttr.ready = function(e) {
                        c.async(function() {
                            e(twttr)
                        })
                    }, twttr.widgets.load()
                })
            })
        })
    }()
});
/* JS manifest
 *

 */

;

