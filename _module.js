function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function create_slot(definition, ctx, $$scope, fn) {
    if (definition) {
        const slot_ctx = get_slot_context(definition, ctx, $$scope, fn);
        return definition[0](slot_ctx);
    }
}
function get_slot_context(definition, ctx, $$scope, fn) {
    return definition[1] && fn
        ? assign($$scope.ctx.slice(), definition[1](fn(ctx)))
        : $$scope.ctx;
}
function get_slot_changes(definition, $$scope, dirty, fn) {
    if (definition[2] && fn) {
        const lets = definition[2](fn(dirty));
        if ($$scope.dirty === undefined) {
            return lets;
        }
        if (typeof lets === 'object') {
            const merged = [];
            const len = Math.max($$scope.dirty.length, lets.length);
            for (let i = 0; i < len; i += 1) {
                merged[i] = $$scope.dirty[i] | lets[i];
            }
            return merged;
        }
        return $$scope.dirty | lets;
    }
    return $$scope.dirty;
}
function update_slot_base(slot, slot_definition, ctx, $$scope, slot_changes, get_slot_context_fn) {
    if (slot_changes) {
        const slot_context = get_slot_context(slot_definition, ctx, $$scope, get_slot_context_fn);
        slot.p(slot_context, slot_changes);
    }
}
function get_all_dirty_from_scope($$scope) {
    if ($$scope.ctx.length > 32) {
        const dirty = [];
        const length = $$scope.ctx.length / 32;
        for (let i = 0; i < length; i++) {
            dirty[i] = -1;
        }
        return dirty;
    }
    return -1;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function action_destroyer(action_result) {
    return action_result && is_function(action_result.destroy) ? action_result.destroy : noop;
}
const contenteditable_truthy_values = ['', true, 1, 'true', 'contenteditable'];

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_data_contenteditable(text, data) {
    data = '' + data;
    if (text.wholeText === data)
        return;
    text.data = data;
}
function set_data_maybe_contenteditable(text, data, attr_value) {
    if (~contenteditable_truthy_values.indexOf(attr_value)) {
        set_data_contenteditable(text, data);
    }
    else {
        set_data(text, data);
    }
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function destroy_block(block, lookup) {
    block.d(1);
    lookup.delete(block.key);
}
function update_keyed_each(old_blocks, dirty, get_key, dynamic, ctx, list, lookup, node, destroy, create_each_block, next, get_context) {
    let o = old_blocks.length;
    let n = list.length;
    let i = o;
    const old_indexes = {};
    while (i--)
        old_indexes[old_blocks[i].key] = i;
    const new_blocks = [];
    const new_lookup = new Map();
    const deltas = new Map();
    const updates = [];
    i = n;
    while (i--) {
        const child_ctx = get_context(ctx, list, i);
        const key = get_key(child_ctx);
        let block = lookup.get(key);
        if (!block) {
            block = create_each_block(key, child_ctx);
            block.c();
        }
        else if (dynamic) {
            // defer updates until all the DOM shuffling is done
            updates.push(() => block.p(child_ctx, dirty));
        }
        new_lookup.set(key, new_blocks[i] = block);
        if (key in old_indexes)
            deltas.set(key, Math.abs(i - old_indexes[key]));
    }
    const will_move = new Set();
    const did_move = new Set();
    function insert(block) {
        transition_in(block, 1);
        block.m(node, next);
        lookup.set(block.key, block);
        next = block.first;
        n--;
    }
    while (o && n) {
        const new_block = new_blocks[n - 1];
        const old_block = old_blocks[o - 1];
        const new_key = new_block.key;
        const old_key = old_block.key;
        if (new_block === old_block) {
            // do nothing
            next = new_block.first;
            o--;
            n--;
        }
        else if (!new_lookup.has(old_key)) {
            // remove old block
            destroy(old_block, lookup);
            o--;
        }
        else if (!lookup.has(new_key) || will_move.has(new_key)) {
            insert(new_block);
        }
        else if (did_move.has(old_key)) {
            o--;
        }
        else if (deltas.get(new_key) > deltas.get(old_key)) {
            did_move.add(new_key);
            insert(new_block);
        }
        else {
            will_move.add(old_key);
            o--;
        }
    }
    while (o--) {
        const old_block = old_blocks[o];
        if (!new_lookup.has(old_block.key))
            destroy(old_block, lookup);
    }
    while (n)
        insert(new_blocks[n - 1]);
    run_all(updates);
    return new_blocks;
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function get_spread_object(spread_props) {
    return typeof spread_props === 'object' && spread_props !== null ? spread_props : {};
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta;
	let link0;
	let link1;
	let link2;
	let style;
	let t;

	return {
		c() {
			meta = element("meta");
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n\tfont-family: 'Montserrat', sans-serif;\n}\n\nbody {\n\t@apply bg-white;\n}\n\nhtml {\n\tscroll-behavior: smooth;\n}");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-lsv7sk', document.head);
			meta = claim_element(head_nodes, "META", { name: true, content: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true, crossorigin: true });
			link2 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n\tfont-family: 'Montserrat', sans-serif;\n}\n\nbody {\n\t@apply bg-white;\n}\n\nhtml {\n\tscroll-behavior: smooth;\n}");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta, "name", "viewport");
			attr(meta, "content", "width=device-width, initial-scale=1.0");
			attr(link0, "rel", "preconnect");
			attr(link0, "href", "https://fonts.googleapis.com");
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.gstatic.com");
			attr(link1, "crossorigin", "");
			attr(link2, "href", "https://fonts.googleapis.com/css2?family=Nunito+Sans:wght@300;400;700&family=Roboto:wght@300;400;500;700;900&display=swap");
			attr(link2, "rel", "stylesheet");
		},
		m(target, anchor) {
			append_hydration(document.head, meta);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta);
			detach(link0);
			detach(link1);
			detach(link2);
			detach(style);
		}
	};
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment, safe_not_equal, {});
	}
}

function cubicOut(t) {
    const f = t - 1.0;
    return f * f * f + 1.0;
}

function slide(node, { delay = 0, duration = 400, easing = cubicOut, axis = 'y' } = {}) {
    const style = getComputedStyle(node);
    const opacity = +style.opacity;
    const primary_property = axis === 'y' ? 'height' : 'width';
    const primary_property_value = parseFloat(style[primary_property]);
    const secondary_properties = axis === 'y' ? ['top', 'bottom'] : ['left', 'right'];
    const capitalized_secondary_properties = secondary_properties.map((e) => `${e[0].toUpperCase()}${e.slice(1)}`);
    const padding_start_value = parseFloat(style[`padding${capitalized_secondary_properties[0]}`]);
    const padding_end_value = parseFloat(style[`padding${capitalized_secondary_properties[1]}`]);
    const margin_start_value = parseFloat(style[`margin${capitalized_secondary_properties[0]}`]);
    const margin_end_value = parseFloat(style[`margin${capitalized_secondary_properties[1]}`]);
    const border_width_start_value = parseFloat(style[`border${capitalized_secondary_properties[0]}Width`]);
    const border_width_end_value = parseFloat(style[`border${capitalized_secondary_properties[1]}Width`]);
    return {
        delay,
        duration,
        easing,
        css: t => 'overflow: hidden;' +
            `opacity: ${Math.min(t * 20, 1) * opacity};` +
            `${primary_property}: ${t * primary_property_value}px;` +
            `padding-${secondary_properties[0]}: ${t * padding_start_value}px;` +
            `padding-${secondary_properties[1]}: ${t * padding_end_value}px;` +
            `margin-${secondary_properties[0]}: ${t * margin_start_value}px;` +
            `margin-${secondary_properties[1]}: ${t * margin_end_value}px;` +
            `border-${secondary_properties[0]}-width: ${t * border_width_start_value}px;` +
            `border-${secondary_properties[1]}-width: ${t * border_width_end_value}px;`
    };
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i];
	child_ctx[5] = i;
	const constants_0 = `line${/*i*/ child_ctx[5] + 1}`;
	child_ctx[3] = constants_0;
	return child_ctx;
}

// (8:2) {#each Array(3) as _, i}
function create_each_block(ctx) {
	let div;
	let div_class_value;

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			children(div).forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", div_class_value = "line " + /*line*/ ctx[3] + " svelte-dqf2xj");
			toggle_class(div, "opened", /*opened*/ ctx[0]);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*opened*/ 1) {
				toggle_class(div, "opened", /*opened*/ ctx[0]);
			}
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$1(ctx) {
	let button;
	let div;
	let mounted;
	let dispose;
	let each_value = Array(3);
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	return {
		c() {
			button = element("button");
			div = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			div = claim_element(button_nodes, "DIV", { class: true });
			var div_nodes = children(div);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div_nodes);
			}

			div_nodes.forEach(detach);
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "icon svelte-dqf2xj");
			attr(button, "class", "burgerButton svelte-dqf2xj");
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			append_hydration(button, div);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div, null);
				}
			}

			if (!mounted) {
				dispose = listen(button, "click", function () {
					if (is_function(/*onClick*/ ctx[1])) /*onClick*/ ctx[1].apply(this, arguments);
				});

				mounted = true;
			}
		},
		p(new_ctx, [dirty]) {
			ctx = new_ctx;

			if (dirty & /*opened*/ 1) {
				each_value = Array(3);
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(button);
			destroy_each(each_blocks, detaching);
			mounted = false;
			dispose();
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { opened } = $$props;
	let { onClick } = $$props;

	$$self.$$set = $$props => {
		if ('opened' in $$props) $$invalidate(0, opened = $$props.opened);
		if ('onClick' in $$props) $$invalidate(1, onClick = $$props.onClick);
	};

	return [opened, onClick];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment$1, safe_not_equal, { opened: 0, onClick: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link.label;
	child_ctx[9] = list[i].link.href;
	return child_ctx;
}

// (125:3) {#if opened}
function create_if_block(ctx) {
	let ul;
	let each_blocks = [];
	let each_1_lookup = new Map();
	let t0;
	let li;
	let button;
	let div;
	let t1;
	let ul_transition;
	let current;
	let each_value = /*navigations*/ ctx[1];
	const get_key = ctx => /*label*/ ctx[8];

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context$1(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block$1(key, child_ctx));
	}

	return {
		c() {
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			li = element("li");
			button = element("button");
			div = element("div");
			t1 = text(/*button_text*/ ctx[2]);
			this.h();
		},
		l(nodes) {
			ul = claim_element(nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			t0 = claim_space(ul_nodes);
			li = claim_element(ul_nodes, "LI", { class: true });
			var li_nodes = children(li);
			button = claim_element(li_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			div = claim_element(button_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t1 = claim_text(div_nodes, /*button_text*/ ctx[2]);
			div_nodes.forEach(detach);
			button_nodes.forEach(detach);
			li_nodes.forEach(detach);
			ul_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "contentContainer svelte-rf5mx7");
			attr(button, "class", "button svelte-rf5mx7");
			attr(li, "class", "buttonWrapper svelte-rf5mx7");
			attr(ul, "class", "navigations svelte-rf5mx7");
		},
		m(target, anchor) {
			insert_hydration(target, ul, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(ul, t0);
			append_hydration(ul, li);
			append_hydration(li, button);
			append_hydration(button, div);
			append_hydration(div, t1);
			current = true;
		},
		p(ctx, dirty) {
			if (dirty & /*navigations*/ 2) {
				each_value = /*navigations*/ ctx[1];
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, ul, destroy_block, create_each_block$1, t0, get_each_context$1);
			}

			if (!current || dirty & /*button_text*/ 4) set_data(t1, /*button_text*/ ctx[2]);
		},
		i(local) {
			if (current) return;

			add_render_callback(() => {
				if (!current) return;
				if (!ul_transition) ul_transition = create_bidirectional_transition(ul, slide, {}, true);
				ul_transition.run(1);
			});

			current = true;
		},
		o(local) {
			if (!ul_transition) ul_transition = create_bidirectional_transition(ul, slide, {}, false);
			ul_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d();
			}

			if (detaching && ul_transition) ul_transition.end();
		}
	};
}

// (127:5) {#each navigations as {link: { label, href }}
function create_each_block$1(key_1, ctx) {
	let li;
	let a;
	let t_value = /*label*/ ctx[8] + "";
	let t;
	let a_href_value;

	return {
		key: key_1,
		first: null,
		c() {
			li = element("li");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*href*/ ctx[9]);
			attr(li, "class", "navigation svelte-rf5mx7");
			this.first = li;
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t);
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if (dirty & /*navigations*/ 2 && t_value !== (t_value = /*label*/ ctx[8] + "")) set_data(t, t_value);

			if (dirty & /*navigations*/ 2 && a_href_value !== (a_href_value = /*href*/ ctx[9])) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

function create_fragment$2(ctx) {
	let div4;
	let header;
	let div3;
	let div0;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let div1;
	let burger;
	let t1;
	let div2;
	let current;
	let mounted;
	let dispose;
	add_render_callback(/*onwindowresize*/ ctx[7]);

	burger = new Component$1({
			props: {
				opened: /*opened*/ ctx[4],
				onClick: /*handleToggleNav*/ ctx[5]
			}
		});

	let if_block = /*opened*/ ctx[4] && create_if_block(ctx);

	return {
		c() {
			div4 = element("div");
			header = element("header");
			div3 = element("div");
			div0 = element("div");
			img = element("img");
			t0 = space();
			div1 = element("div");
			create_component(burger.$$.fragment);
			t1 = space();
			div2 = element("div");
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			header = claim_element(div4_nodes, "HEADER", {});
			var header_nodes = children(header);
			div3 = claim_element(header_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", {});
			var div0_nodes = children(div0);
			img = claim_element(div0_nodes, "IMG", { class: true, src: true, alt: true });
			div0_nodes.forEach(detach);
			t0 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			claim_component(burger.$$.fragment, div1_nodes);
			div1_nodes.forEach(detach);
			t1 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			if (if_block) if_block.l(div2_nodes);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "class", "logo svelte-rf5mx7");
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].src)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].description);
			attr(div1, "class", "burgerWrapper svelte-rf5mx7");
			attr(div2, "class", "navigationContainer svelte-rf5mx7");
			attr(div3, "class", "header svelte-rf5mx7");
			attr(div4, "class", "section");
			attr(div4, "id", "section-dd14c65e");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, header);
			append_hydration(header, div3);
			append_hydration(div3, div0);
			append_hydration(div0, img);
			append_hydration(div3, t0);
			append_hydration(div3, div1);
			mount_component(burger, div1, null);
			append_hydration(div3, t1);
			append_hydration(div3, div2);
			if (if_block) if_block.m(div2, null);
			current = true;

			if (!mounted) {
				dispose = listen(window, "resize", /*onwindowresize*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].src)) {
				attr(img, "src", img_src_value);
			}

			if (!current || dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].description)) {
				attr(img, "alt", img_alt_value);
			}

			const burger_changes = {};
			if (dirty & /*opened*/ 16) burger_changes.opened = /*opened*/ ctx[4];
			burger.$set(burger_changes);

			if (/*opened*/ ctx[4]) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*opened*/ 16) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div2, null);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(burger.$$.fragment, local);
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(burger.$$.fragment, local);
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);
			destroy_component(burger);
			if (if_block) if_block.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let isDesktop;
	let { logo } = $$props;
	let { navigations } = $$props;
	let { button_text } = $$props;

	function handleToggleNav() {
		$$invalidate(4, opened = !opened);
	}

	let opened = false;
	let innerWidth = 0;

	function onwindowresize() {
		$$invalidate(3, innerWidth = window.innerWidth);
	}

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('navigations' in $$props) $$invalidate(1, navigations = $$props.navigations);
		if ('button_text' in $$props) $$invalidate(2, button_text = $$props.button_text);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*innerWidth*/ 8) {
			 $$invalidate(6, isDesktop = innerWidth > 1023);
		}

		if ($$self.$$.dirty & /*isDesktop*/ 64) {
			 {
				if (isDesktop) {
					$$invalidate(4, opened = true);
				}
			}
		}
	};

	return [
		logo,
		navigations,
		button_text,
		innerWidth,
		opened,
		handleToggleNav,
		isDesktop,
		onwindowresize
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$2, safe_not_equal, { logo: 0, navigations: 1, button_text: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].content;
	child_ctx[5] = i;
	return child_ctx;
}

// (70:12) {:else}
function create_else_block(ctx) {
	let t_value = /*content*/ ctx[3] + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*sub_titles*/ 1 && t_value !== (t_value = /*content*/ ctx[3] + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (68:5) {#if i === 0}
function create_if_block$1(ctx) {
	let strong;
	let t_value = /*content*/ ctx[3] + "";
	let t;

	return {
		c() {
			strong = element("strong");
			t = text(t_value);
		},
		l(nodes) {
			strong = claim_element(nodes, "STRONG", {});
			var strong_nodes = children(strong);
			t = claim_text(strong_nodes, t_value);
			strong_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, strong, anchor);
			append_hydration(strong, t);
		},
		p(ctx, dirty) {
			if (dirty & /*sub_titles*/ 1 && t_value !== (t_value = /*content*/ ctx[3] + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(strong);
		}
	};
}

// (66:3) {#each sub_titles as { content }
function create_each_block$2(key_1, ctx) {
	let p;
	let t;

	function select_block_type(ctx, dirty) {
		if (/*i*/ ctx[5] === 0) return create_if_block$1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		key: key_1,
		first: null,
		c() {
			p = element("p");
			if_block.c();
			t = space();
			this.h();
		},
		l(nodes) {
			p = claim_element(nodes, "P", { class: true });
			var p_nodes = children(p);
			if_block.l(p_nodes);
			t = claim_space(p_nodes);
			p_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p, "class", "subTitle svelte-1cwnrqb");
			this.first = p;
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			if_block.m(p, null);
			append_hydration(p, t);
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;

			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(p, t);
				}
			}
		},
		d(detaching) {
			if (detaching) detach(p);
			if_block.d();
		}
	};
}

function create_fragment$3(ctx) {
	let div1;
	let section;
	let div0;
	let h2;
	let t0;
	let t1;
	let each_blocks = [];
	let each_1_lookup = new Map();
	let t2;
	let figure;
	let img;
	let img_src_value;
	let img_alt_value;
	let img_width_value;
	let img_height_value;
	let each_value = /*sub_titles*/ ctx[0];
	const get_key = ctx => /*i*/ ctx[5];

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context$2(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block$2(key, child_ctx));
	}

	return {
		c() {
			div1 = element("div");
			section = element("section");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*title*/ ctx[2]);
			t1 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			figure = element("figure");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true, id: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*title*/ ctx[2]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			figure = claim_element(section_nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);

			img = claim_element(figure_nodes, "IMG", {
				src: true,
				alt: true,
				width: true,
				height: true
			});

			figure_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "title svelte-1cwnrqb");
			attr(div0, "class", "sectionTitle svelte-1cwnrqb");
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[1].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[1].description);
			attr(img, "width", img_width_value = 1482);
			attr(img, "height", img_height_value = 780);
			attr(figure, "class", "imageContainer svelte-1cwnrqb");
			attr(section, "class", "sectionContainer svelte-1cwnrqb");
			attr(section, "id", "foundation");
			attr(div1, "class", "section");
			attr(div1, "id", "section-aab805d3");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}

			append_hydration(section, t2);
			append_hydration(section, figure);
			append_hydration(figure, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*title*/ 4) set_data(t0, /*title*/ ctx[2]);

			if (dirty & /*sub_titles*/ 1) {
				each_value = /*sub_titles*/ ctx[0];
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, div0, destroy_block, create_each_block$2, null, get_each_context$2);
			}

			if (dirty & /*image*/ 2 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[1].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 2 && img_alt_value !== (img_alt_value = /*image*/ ctx[1].description)) {
				attr(img, "alt", img_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d();
			}
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { sub_titles } = $$props;
	let { image } = $$props;
	let { title } = $$props;

	$$self.$$set = $$props => {
		if ('sub_titles' in $$props) $$invalidate(0, sub_titles = $$props.sub_titles);
		if ('image' in $$props) $$invalidate(1, image = $$props.image);
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
	};

	return [sub_titles, image, title];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$2, create_fragment$3, safe_not_equal, { sub_titles: 0, image: 1, title: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i].content;
	child_ctx[3] = list[i].props;
	child_ctx[5] = i;
	return child_ctx;
}

// (14:1) {#each subTitles as { content, props }
function create_each_block$3(key_1, ctx) {
	let p;
	let t0_value = /*content*/ ctx[2] + "";
	let t0;
	let t1;
	let p_levels = [/*props*/ ctx[3], { class: "subTitle" }];
	let p_data = {};

	for (let i = 0; i < p_levels.length; i += 1) {
		p_data = assign(p_data, p_levels[i]);
	}

	return {
		key: key_1,
		first: null,
		c() {
			p = element("p");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			p = claim_element(nodes, "P", { class: true });
			var p_nodes = children(p);
			t0 = claim_text(p_nodes, t0_value);
			t1 = claim_space(p_nodes);
			p_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(p, p_data);
			toggle_class(p, "svelte-17auxc5", true);
			this.first = p;
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t0);
			append_hydration(p, t1);
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if (dirty & /*subTitles*/ 2 && t0_value !== (t0_value = /*content*/ ctx[2] + "")) set_data_maybe_contenteditable(t0, t0_value, p_data['contenteditable']);
			set_attributes(p, p_data = get_spread_update(p_levels, [dirty & /*subTitles*/ 2 && /*props*/ ctx[3], { class: "subTitle" }]));
			toggle_class(p, "svelte-17auxc5", true);
		},
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

function create_fragment$4(ctx) {
	let div;
	let h2;
	let t0;
	let t1;
	let each_blocks = [];
	let each_1_lookup = new Map();
	let each_value = /*subTitles*/ ctx[1];
	const get_key = ctx => /*i*/ ctx[5];

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context$3(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block$3(key, child_ctx));
	}

	return {
		c() {
			div = element("div");
			h2 = element("h2");
			t0 = text(/*title*/ ctx[0]);
			t1 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			h2 = claim_element(div_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*title*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div_nodes);
			}

			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "title svelte-17auxc5");
			attr(div, "class", "sectionTitle svelte-17auxc5");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, h2);
			append_hydration(h2, t0);
			append_hydration(div, t1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*title*/ 1) set_data(t0, /*title*/ ctx[0]);

			if (dirty & /*subTitles*/ 2) {
				each_value = /*subTitles*/ ctx[1];
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, div, destroy_block, create_each_block$3, null, get_each_context$3);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d();
			}
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { subTitles } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('subTitles' in $$props) $$invalidate(1, subTitles = $$props.subTitles);
	};

	return [title, subTitles];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$3, create_fragment$4, safe_not_equal, { title: 0, subTitles: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i].activities;
	child_ctx[5] = list[i].timeRange;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i];
	return child_ctx;
}

const get_headerIcon_slot_changes = dirty => ({});
const get_headerIcon_slot_context = ctx => ({});

// (21:4) {#each activities as activity}
function create_each_block_1(ctx) {
	let div;
	let t_value = /*activity*/ ctx[8] + "";
	let t;

	return {
		c() {
			div = element("div");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t = claim_text(div_nodes, t_value);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "mb-[5px]");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 2 && t_value !== (t_value = /*activity*/ ctx[8] + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (18:2) {#each data as { activities, timeRange }
function create_each_block$4(key_1, ctx) {
	let div0;
	let t0_value = /*timeRange*/ ctx[5] + "";
	let t0;
	let t1;
	let div1;
	let t2;
	let each_value_1 = /*activities*/ ctx[4];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	return {
		key: key_1,
		first: null,
		c() {
			div0 = element("div");
			t0 = text(t0_value);
			t1 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			this.h();
		},
		l(nodes) {
			div0 = claim_element(nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t0 = claim_text(div0_nodes, t0_value);
			div0_nodes.forEach(detach);
			t1 = claim_space(nodes);
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			t2 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "scheduleTime svelte-1u79v31");
			attr(div1, "class", "scheduleActivities svelte-1u79v31");
			this.first = div0;
		},
		m(target, anchor) {
			insert_hydration(target, div0, anchor);
			append_hydration(div0, t0);
			insert_hydration(target, t1, anchor);
			insert_hydration(target, div1, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(div1, t2);
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if (dirty & /*data*/ 2 && t0_value !== (t0_value = /*timeRange*/ ctx[5] + "")) set_data(t0, t0_value);

			if (dirty & /*data*/ 2) {
				each_value_1 = /*activities*/ ctx[4];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div1, t2);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		d(detaching) {
			if (detaching) detach(div0);
			if (detaching) detach(t1);
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function create_fragment$5(ctx) {
	let div1;
	let header;
	let t0;
	let h3;
	let t1;
	let t2;
	let div0;
	let each_blocks = [];
	let each_1_lookup = new Map();
	let current;
	const headerIcon_slot_template = /*#slots*/ ctx[3].headerIcon;
	const headerIcon_slot = create_slot(headerIcon_slot_template, ctx, /*$$scope*/ ctx[2], get_headerIcon_slot_context);
	let each_value = /*data*/ ctx[1];
	const get_key = ctx => /*timeRange*/ ctx[5];

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context$4(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block$4(key, child_ctx));
	}

	return {
		c() {
			div1 = element("div");
			header = element("header");
			if (headerIcon_slot) headerIcon_slot.c();
			t0 = space();
			h3 = element("h3");
			t1 = text(/*title*/ ctx[0]);
			t2 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			header = claim_element(div1_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			if (headerIcon_slot) headerIcon_slot.l(header_nodes);
			t0 = claim_space(header_nodes);
			h3 = claim_element(header_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, /*title*/ ctx[0]);
			h3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "headerTitle svelte-1u79v31");
			attr(header, "class", "scheduleHeader svelte-1u79v31");
			attr(div0, "class", "scheduleBody svelte-1u79v31");
			attr(div1, "class", "schedule svelte-1u79v31");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, header);

			if (headerIcon_slot) {
				headerIcon_slot.m(header, null);
			}

			append_hydration(header, t0);
			append_hydration(header, h3);
			append_hydration(h3, t1);
			append_hydration(div1, t2);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (headerIcon_slot) {
				if (headerIcon_slot.p && (!current || dirty & /*$$scope*/ 4)) {
					update_slot_base(
						headerIcon_slot,
						headerIcon_slot_template,
						ctx,
						/*$$scope*/ ctx[2],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[2])
						: get_slot_changes(headerIcon_slot_template, /*$$scope*/ ctx[2], dirty, get_headerIcon_slot_changes),
						get_headerIcon_slot_context
					);
				}
			}

			if (!current || dirty & /*title*/ 1) set_data(t1, /*title*/ ctx[0]);

			if (dirty & /*data*/ 2) {
				each_value = /*data*/ ctx[1];
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, div0, destroy_block, create_each_block$4, null, get_each_context$4);
			}
		},
		i(local) {
			if (current) return;
			transition_in(headerIcon_slot, local);
			current = true;
		},
		o(local) {
			transition_out(headerIcon_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			if (headerIcon_slot) headerIcon_slot.d(detaching);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d();
			}
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;
	let { title } = $$props;
	let { data } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('data' in $$props) $$invalidate(1, data = $$props.data);
		if ('$$scope' in $$props) $$invalidate(2, $$scope = $$props.$$scope);
	};

	return [title, data, $$scope, slots];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, create_fragment$5, safe_not_equal, { title: 0, data: 1 });
	}
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block$2(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block$1;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block$1(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$6(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block$2(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$2(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$5, create_fragment$6, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$5(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i].title;
	child_ctx[4] = list[i].iconify;
	child_ctx[5] = list[i].data !== undefined ? list[i].data : [];

	const constants_0 = /*primoData*/ child_ctx[5].map(({ time_range, activities }) => ({
		timeRange: time_range,
		activities: activities.map(it => it.activity)
	}));

	child_ctx[6] = constants_0;
	return child_ctx;
}

// (65:16) 
function create_headerIcon_slot(ctx) {
	let icon;
	let current;
	const icon_spread_levels = [/*iconify*/ ctx[4], { slot: "headerIcon" }];
	let icon_props = {};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$6({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = (dirty & /*schedule*/ 2)
			? get_spread_update(icon_spread_levels, [get_spread_object(/*iconify*/ ctx[4]), icon_spread_levels[1]])
			: {};

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (62:12) {#each schedule as {title, iconify, data: primoData = []}}
function create_each_block$5(ctx) {
	let schedule_1;
	let current;

	schedule_1 = new Component$5({
			props: {
				title: /*title*/ ctx[2],
				data: /*data*/ ctx[6],
				$$slots: { headerIcon: [create_headerIcon_slot] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			create_component(schedule_1.$$.fragment);
		},
		l(nodes) {
			claim_component(schedule_1.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(schedule_1, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const schedule_1_changes = {};
			if (dirty & /*schedule*/ 2) schedule_1_changes.title = /*title*/ ctx[2];
			if (dirty & /*schedule*/ 2) schedule_1_changes.data = /*data*/ ctx[6];

			if (dirty & /*$$scope, schedule*/ 514) {
				schedule_1_changes.$$scope = { dirty, ctx };
			}

			schedule_1.$set(schedule_1_changes);
		},
		i(local) {
			if (current) return;
			transition_in(schedule_1.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(schedule_1.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(schedule_1, detaching);
		}
	};
}

function create_fragment$7(ctx) {
	let div4;
	let section;
	let div3;
	let div1;
	let sectiontitle;
	let t0;
	let div0;
	let video_1;
	let track;
	let source;
	let source_src_value;
	let t1;
	let div2;
	let current;

	sectiontitle = new Component$4({
			props: {
				title: /*title*/ ctx[2],
				subTitles: /*sub_titles*/ ctx[0]
			}
		});

	let each_value = /*schedule*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$5(get_each_context$5(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div4 = element("div");
			section = element("section");
			div3 = element("div");
			div1 = element("div");
			create_component(sectiontitle.$$.fragment);
			t0 = space();
			div0 = element("div");
			video_1 = element("video");
			track = element("track");
			source = element("source");
			t1 = space();
			div2 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			section = claim_element(div4_nodes, "SECTION", { class: true, id: true });
			var section_nodes = children(section);
			div3 = claim_element(section_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			claim_component(sectiontitle.$$.fragment, div1_nodes);
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			video_1 = claim_element(div0_nodes, "VIDEO", {});
			var video_1_nodes = children(video_1);
			track = claim_element(video_1_nodes, "TRACK", { kind: true });
			source = claim_element(video_1_nodes, "SOURCE", { src: true, type: true });
			video_1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t1 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div2_nodes);
			}

			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(track, "kind", "captions");
			track.default = true;
			if (!src_url_equal(source.src, source_src_value = "https://ilo.edu.vn/storage/app/media/giaoducmamnon/video/ILO-videos.mp4")) attr(source, "src", source_src_value);
			attr(source, "type", "video/mp4");
			video_1.controls = true;
			attr(div0, "class", "videoContainer svelte-1p2w3ro");
			attr(div1, "class", "contentContainer svelte-1p2w3ro");
			attr(div2, "class", "scheduleContainer svelte-1p2w3ro");
			attr(div3, "class", "container svelte-1p2w3ro");
			attr(section, "class", "sectionWrapper svelte-1p2w3ro");
			attr(section, "id", "aDayAtOurSchool");
			attr(div4, "class", "section");
			attr(div4, "id", "section-61bedf82");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, section);
			append_hydration(section, div3);
			append_hydration(div3, div1);
			mount_component(sectiontitle, div1, null);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			append_hydration(div0, video_1);
			append_hydration(video_1, track);
			append_hydration(video_1, source);
			append_hydration(div3, t1);
			append_hydration(div3, div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div2, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			const sectiontitle_changes = {};
			if (dirty & /*title*/ 4) sectiontitle_changes.title = /*title*/ ctx[2];
			if (dirty & /*sub_titles*/ 1) sectiontitle_changes.subTitles = /*sub_titles*/ ctx[0];
			sectiontitle.$set(sectiontitle_changes);

			if (dirty & /*schedule*/ 2) {
				each_value = /*schedule*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$5(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$5(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div2, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(sectiontitle.$$.fragment, local);

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			transition_out(sectiontitle.$$.fragment, local);
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);
			destroy_component(sectiontitle);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { sub_titles } = $$props;
	let { video } = $$props;
	let { schedule } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('sub_titles' in $$props) $$invalidate(0, sub_titles = $$props.sub_titles);
		if ('video' in $$props) $$invalidate(3, video = $$props.video);
		if ('schedule' in $$props) $$invalidate(1, schedule = $$props.schedule);
	};

	return [sub_titles, schedule, title, video];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$7, safe_not_equal, {
			title: 2,
			sub_titles: 0,
			video: 3,
			schedule: 1
		});
	}
}

function isObject(subject) {
  return Object.prototype.toString.call(subject) === "[object Object]";
}
function isRecord(subject) {
  return isObject(subject) || Array.isArray(subject);
}
function canUseDOM() {
  return !!(typeof window !== "undefined" && window.document && window.document.createElement);
}
function areOptionsEqual(optionsA, optionsB) {
  const optionsAKeys = Object.keys(optionsA);
  const optionsBKeys = Object.keys(optionsB);
  if (optionsAKeys.length !== optionsBKeys.length)
    return false;
  const breakpointsA = JSON.stringify(Object.keys(optionsA.breakpoints || {}));
  const breakpointsB = JSON.stringify(Object.keys(optionsB.breakpoints || {}));
  if (breakpointsA !== breakpointsB)
    return false;
  return optionsAKeys.every((key) => {
    const valueA = optionsA[key];
    const valueB = optionsB[key];
    if (typeof valueA === "function")
      return `${valueA}` === `${valueB}`;
    if (!isRecord(valueA) || !isRecord(valueB))
      return valueA === valueB;
    return areOptionsEqual(valueA, valueB);
  });
}
function sortAndMapPluginToOptions(plugins) {
  return plugins.concat().sort((a, b) => a.name > b.name ? 1 : -1).map((plugin) => plugin.options);
}
function arePluginsEqual(pluginsA, pluginsB) {
  if (pluginsA.length !== pluginsB.length)
    return false;
  const optionsA = sortAndMapPluginToOptions(pluginsA);
  const optionsB = sortAndMapPluginToOptions(pluginsB);
  return optionsA.every((optionA, index) => {
    const optionB = optionsB[index];
    return areOptionsEqual(optionA, optionB);
  });
}

function isNumber(subject) {
  return typeof subject === "number";
}
function isString(subject) {
  return typeof subject === "string";
}
function isBoolean(subject) {
  return typeof subject === "boolean";
}
function isObject$1(subject) {
  return Object.prototype.toString.call(subject) === "[object Object]";
}
function mathAbs(n) {
  return Math.abs(n);
}
function mathSign(n) {
  return Math.sign(n);
}
function deltaAbs(valueB, valueA) {
  return mathAbs(valueB - valueA);
}
function factorAbs(valueB, valueA) {
  if (valueB === 0 || valueA === 0)
    return 0;
  if (mathAbs(valueB) <= mathAbs(valueA))
    return 0;
  const diff = deltaAbs(mathAbs(valueB), mathAbs(valueA));
  return mathAbs(diff / valueB);
}
function arrayKeys(array) {
  return objectKeys(array).map(Number);
}
function arrayLast(array) {
  return array[arrayLastIndex(array)];
}
function arrayLastIndex(array) {
  return Math.max(0, array.length - 1);
}
function objectKeys(object) {
  return Object.keys(object);
}
function objectsMergeDeep(objectA, objectB) {
  return [objectA, objectB].reduce((mergedObjects, currentObject) => {
    objectKeys(currentObject).forEach((key) => {
      const valueA = mergedObjects[key];
      const valueB = currentObject[key];
      const areObjects = isObject$1(valueA) && isObject$1(valueB);
      mergedObjects[key] = areObjects ? objectsMergeDeep(valueA, valueB) : valueB;
    });
    return mergedObjects;
  }, {});
}
function isMouseEvent(evt, ownerWindow) {
  return typeof ownerWindow.MouseEvent !== "undefined" && evt instanceof ownerWindow.MouseEvent;
}
function Alignment(align, viewSize) {
  const predefined = {
    start,
    center,
    end
  };
  function start() {
    return 0;
  }
  function center(n) {
    return end(n) / 2;
  }
  function end(n) {
    return viewSize - n;
  }
  function percent() {
    return viewSize * Number(align);
  }
  function measure(n) {
    if (isNumber(align))
      return percent();
    return predefined[align](n);
  }
  const self = {
    measure
  };
  return self;
}
function Axis(axis, direction) {
  const scroll = axis === "y" ? "y" : "x";
  const cross = axis === "y" ? "x" : "y";
  const startEdge = getStartEdge();
  const endEdge = getEndEdge();
  function measureSize(rect) {
    const {
      width,
      height
    } = rect;
    return scroll === "x" ? width : height;
  }
  function getStartEdge() {
    if (scroll === "y")
      return "top";
    return direction === "rtl" ? "right" : "left";
  }
  function getEndEdge() {
    if (scroll === "y")
      return "bottom";
    return direction === "rtl" ? "left" : "right";
  }
  const self = {
    scroll,
    cross,
    startEdge,
    endEdge,
    measureSize
  };
  return self;
}
function Limit(min, max) {
  const length = mathAbs(min - max);
  function reachedMin(n) {
    return n < min;
  }
  function reachedMax(n) {
    return n > max;
  }
  function reachedAny(n) {
    return reachedMin(n) || reachedMax(n);
  }
  function constrain(n) {
    if (!reachedAny(n))
      return n;
    return reachedMin(n) ? min : max;
  }
  function removeOffset(n) {
    if (!length)
      return n;
    return n - length * Math.ceil((n - max) / length);
  }
  const self = {
    length,
    max,
    min,
    constrain,
    reachedAny,
    reachedMax,
    reachedMin,
    removeOffset
  };
  return self;
}
function Counter(max, start, loop) {
  const {
    constrain
  } = Limit(0, max);
  const loopEnd = max + 1;
  let counter = withinLimit(start);
  function withinLimit(n) {
    return !loop ? constrain(n) : mathAbs((loopEnd + n) % loopEnd);
  }
  function get() {
    return counter;
  }
  function set(n) {
    counter = withinLimit(n);
    return self;
  }
  function add(n) {
    return clone().set(get() + n);
  }
  function clone() {
    return Counter(max, get(), loop);
  }
  const self = {
    get,
    set,
    add,
    clone
  };
  return self;
}
function Direction(direction) {
  const sign = direction === "rtl" ? -1 : 1;
  function apply(n) {
    return n * sign;
  }
  const self = {
    apply
  };
  return self;
}
function EventStore() {
  let listeners = [];
  function add(node, type, handler, options = {
    passive: true
  }) {
    node.addEventListener(type, handler, options);
    listeners.push(() => node.removeEventListener(type, handler, options));
    return self;
  }
  function clear() {
    listeners = listeners.filter((remove) => remove());
  }
  const self = {
    add,
    clear
  };
  return self;
}
function DragHandler(axis, direction, rootNode, ownerDocument, ownerWindow, target, dragTracker, location, animation, scrollTo, scrollBody, scrollTarget, index, eventHandler, percentOfView, dragFree, dragThreshold, skipSnaps, baseFriction) {
  const {
    cross: crossAxis
  } = axis;
  const focusNodes = ["INPUT", "SELECT", "TEXTAREA"];
  const nonPassiveEvent = {
    passive: false
  };
  const initEvents = EventStore();
  const dragEvents = EventStore();
  const goToNextThreshold = Limit(50, 225).constrain(percentOfView.measure(20));
  const snapForceBoost = {
    mouse: 300,
    touch: 400
  };
  const freeForceBoost = {
    mouse: 500,
    touch: 600
  };
  const baseSpeed = dragFree ? 43 : 25;
  let isMoving = false;
  let startScroll = 0;
  let startCross = 0;
  let pointerIsDown = false;
  let preventScroll = false;
  let preventClick = false;
  let isMouse = false;
  function init(emblaApi, watchDrag) {
    if (!watchDrag)
      return;
    function downIfAllowed(evt) {
      if (isBoolean(watchDrag) || watchDrag(emblaApi, evt))
        down(evt);
    }
    const node = rootNode;
    initEvents.add(node, "dragstart", (evt) => evt.preventDefault(), nonPassiveEvent).add(node, "touchmove", () => void 0, nonPassiveEvent).add(node, "touchend", () => void 0).add(node, "touchstart", downIfAllowed).add(node, "mousedown", downIfAllowed).add(node, "touchcancel", up).add(node, "contextmenu", up).add(node, "click", click, true);
  }
  function destroy() {
    initEvents.clear();
    dragEvents.clear();
  }
  function addDragEvents() {
    const node = isMouse ? ownerDocument : rootNode;
    dragEvents.add(node, "touchmove", move, nonPassiveEvent).add(node, "touchend", up).add(node, "mousemove", move, nonPassiveEvent).add(node, "mouseup", up);
  }
  function isFocusNode(node) {
    const nodeName = node.nodeName || "";
    return focusNodes.includes(nodeName);
  }
  function forceBoost() {
    const boost = dragFree ? freeForceBoost : snapForceBoost;
    const type = isMouse ? "mouse" : "touch";
    return boost[type];
  }
  function allowedForce(force, targetChanged) {
    const next = index.add(mathSign(force) * -1);
    const baseForce = scrollTarget.byDistance(force, !dragFree).distance;
    if (dragFree || mathAbs(force) < goToNextThreshold)
      return baseForce;
    if (skipSnaps && targetChanged)
      return baseForce * 0.5;
    return scrollTarget.byIndex(next.get(), 0).distance;
  }
  function down(evt) {
    const isMouseEvt = isMouseEvent(evt, ownerWindow);
    isMouse = isMouseEvt;
    if (isMouseEvt && evt.button !== 0)
      return;
    if (isFocusNode(evt.target))
      return;
    preventClick = dragFree && isMouseEvt && !evt.buttons && isMoving;
    isMoving = deltaAbs(target.get(), location.get()) >= 2;
    pointerIsDown = true;
    dragTracker.pointerDown(evt);
    scrollBody.useFriction(0).useDuration(0);
    target.set(location);
    addDragEvents();
    startScroll = dragTracker.readPoint(evt);
    startCross = dragTracker.readPoint(evt, crossAxis);
    eventHandler.emit("pointerDown");
  }
  function move(evt) {
    const lastScroll = dragTracker.readPoint(evt);
    const lastCross = dragTracker.readPoint(evt, crossAxis);
    const diffScroll = deltaAbs(lastScroll, startScroll);
    const diffCross = deltaAbs(lastCross, startCross);
    if (!preventScroll && !isMouse) {
      if (!evt.cancelable)
        return up(evt);
      preventScroll = diffScroll > diffCross;
      if (!preventScroll)
        return up(evt);
    }
    const diff = dragTracker.pointerMove(evt);
    if (diffScroll > dragThreshold)
      preventClick = true;
    scrollBody.useFriction(0.3).useDuration(1);
    animation.start();
    target.add(direction.apply(diff));
    evt.preventDefault();
  }
  function up(evt) {
    const currentLocation = scrollTarget.byDistance(0, false);
    const targetChanged = currentLocation.index !== index.get();
    const rawForce = dragTracker.pointerUp(evt) * forceBoost();
    const force = allowedForce(direction.apply(rawForce), targetChanged);
    const forceFactor = factorAbs(rawForce, force);
    const speed = baseSpeed - 10 * forceFactor;
    const friction = baseFriction + forceFactor / 50;
    preventScroll = false;
    pointerIsDown = false;
    dragEvents.clear();
    scrollBody.useDuration(speed).useFriction(friction);
    scrollTo.distance(force, !dragFree);
    isMouse = false;
    eventHandler.emit("pointerUp");
  }
  function click(evt) {
    if (preventClick) {
      evt.stopPropagation();
      evt.preventDefault();
    }
  }
  function pointerDown() {
    return pointerIsDown;
  }
  const self = {
    init,
    pointerDown,
    destroy
  };
  return self;
}
function DragTracker(axis, ownerWindow) {
  const logInterval = 170;
  let startEvent;
  let lastEvent;
  function readTime(evt) {
    return evt.timeStamp;
  }
  function readPoint(evt, evtAxis) {
    const property = evtAxis || axis.scroll;
    const coord = `client${property === "x" ? "X" : "Y"}`;
    return (isMouseEvent(evt, ownerWindow) ? evt : evt.touches[0])[coord];
  }
  function pointerDown(evt) {
    startEvent = evt;
    lastEvent = evt;
    return readPoint(evt);
  }
  function pointerMove(evt) {
    const diff = readPoint(evt) - readPoint(lastEvent);
    const expired = readTime(evt) - readTime(startEvent) > logInterval;
    lastEvent = evt;
    if (expired)
      startEvent = evt;
    return diff;
  }
  function pointerUp(evt) {
    if (!startEvent || !lastEvent)
      return 0;
    const diffDrag = readPoint(lastEvent) - readPoint(startEvent);
    const diffTime = readTime(evt) - readTime(startEvent);
    const expired = readTime(evt) - readTime(lastEvent) > logInterval;
    const force = diffDrag / diffTime;
    const isFlick = diffTime && !expired && mathAbs(force) > 0.1;
    return isFlick ? force : 0;
  }
  const self = {
    pointerDown,
    pointerMove,
    pointerUp,
    readPoint
  };
  return self;
}
function PercentOfView(viewSize) {
  function measure(n) {
    return viewSize * (n / 100);
  }
  const self = {
    measure
  };
  return self;
}
function ResizeHandler(container, eventHandler, ownerWindow, slides, axis) {
  let resizeObserver;
  let containerSize;
  let slideSizes = [];
  let destroyed = false;
  function readSize(node) {
    return axis.measureSize(node.getBoundingClientRect());
  }
  function init(emblaApi, watchResize) {
    if (!watchResize)
      return;
    containerSize = readSize(container);
    slideSizes = slides.map(readSize);
    function defaultCallback(entries) {
      for (const entry of entries) {
        const isContainer = entry.target === container;
        const slideIndex = slides.indexOf(entry.target);
        const lastSize = isContainer ? containerSize : slideSizes[slideIndex];
        const newSize = readSize(isContainer ? container : slides[slideIndex]);
        if (lastSize !== newSize) {
          ownerWindow.requestAnimationFrame(() => {
            emblaApi.reInit();
            eventHandler.emit("resize");
          });
          break;
        }
      }
    }
    resizeObserver = new ResizeObserver((entries) => {
      if (destroyed)
        return;
      if (isBoolean(watchResize) || watchResize(emblaApi, entries)) {
        defaultCallback(entries);
      }
    });
    const observeNodes = [container].concat(slides);
    observeNodes.forEach((node) => resizeObserver.observe(node));
  }
  function destroy() {
    if (resizeObserver)
      resizeObserver.disconnect();
    destroyed = true;
  }
  const self = {
    init,
    destroy
  };
  return self;
}
function ScrollBody(location, target, baseDuration, baseFriction) {
  let hasSettled = true;
  let bodyVelocity = 0;
  let scrollDirection = 0;
  let duration = baseDuration;
  let friction = baseFriction;
  function seek() {
    const diff = target.get() - location.get();
    const isInstant = !friction || !duration;
    if (isInstant) {
      bodyVelocity = 0;
      location.set(target);
    } else {
      bodyVelocity += diff / duration;
      bodyVelocity *= friction;
      location.add(bodyVelocity);
    }
    scrollDirection = mathSign(bodyVelocity || diff);
    hasSettled = mathAbs(diff) < 1e-3;
    return self;
  }
  function settled() {
    if (hasSettled)
      location.set(target);
    return hasSettled;
  }
  function velocity() {
    return bodyVelocity;
  }
  function direction() {
    return scrollDirection;
  }
  function useBaseDuration() {
    return useDuration(baseDuration);
  }
  function useBaseFriction() {
    return useFriction(baseFriction);
  }
  function useDuration(n) {
    duration = n;
    return self;
  }
  function useFriction(n) {
    friction = n;
    return self;
  }
  const self = {
    direction,
    seek,
    settled,
    useBaseFriction,
    useBaseDuration,
    useFriction,
    useDuration,
    velocity
  };
  return self;
}
function ScrollBounds(limit, location, target, scrollBody, percentOfView) {
  const pullBackThreshold = percentOfView.measure(10);
  const edgeOffsetTolerance = percentOfView.measure(50);
  const frictionLimit = Limit(0.1, 0.99);
  let disabled = false;
  function shouldConstrain() {
    if (disabled)
      return false;
    if (!limit.reachedAny(target.get()))
      return false;
    if (!limit.reachedAny(location.get()))
      return false;
    return true;
  }
  function constrain(pointerDown) {
    if (!shouldConstrain())
      return;
    const edge = limit.reachedMin(location.get()) ? "min" : "max";
    const diffToEdge = mathAbs(limit[edge] - location.get());
    const diffToTarget = target.get() - location.get();
    const friction = frictionLimit.constrain(diffToEdge / edgeOffsetTolerance);
    target.subtract(diffToTarget * friction);
    if (!pointerDown && mathAbs(diffToTarget) < pullBackThreshold) {
      target.set(limit.constrain(target.get()));
      scrollBody.useDuration(25).useBaseFriction();
    }
  }
  function toggleActive(active) {
    disabled = !active;
  }
  const self = {
    constrain,
    toggleActive
  };
  return self;
}
function ScrollContain(viewSize, contentSize, snapsAligned, containScroll) {
  const scrollBounds = Limit(-contentSize + viewSize, snapsAligned[0]);
  const snapsBounded = measureBounded();
  const snapsContained = measureContained();
  function findDuplicates() {
    const startSnap = snapsBounded[0];
    const endSnap = arrayLast(snapsBounded);
    const min = snapsBounded.lastIndexOf(startSnap);
    const max = snapsBounded.indexOf(endSnap) + 1;
    return Limit(min, max);
  }
  function measureBounded() {
    return snapsAligned.map(scrollBounds.constrain).map((scrollBound) => parseFloat(scrollBound.toFixed(3)));
  }
  function measureContained() {
    if (contentSize <= viewSize)
      return [scrollBounds.max];
    if (containScroll === "keepSnaps")
      return snapsBounded;
    const {
      min,
      max
    } = findDuplicates();
    return snapsBounded.slice(min, max);
  }
  const self = {
    snapsContained
  };
  return self;
}
function ScrollLimit(contentSize, scrollSnaps, loop) {
  const max = scrollSnaps[0];
  const min = loop ? max - contentSize : arrayLast(scrollSnaps);
  const limit = Limit(min, max);
  const self = {
    limit
  };
  return self;
}
function ScrollLooper(contentSize, limit, location, vectors) {
  const jointSafety = 0.1;
  const min = limit.min + jointSafety;
  const max = limit.max + jointSafety;
  const {
    reachedMin,
    reachedMax
  } = Limit(min, max);
  function shouldLoop(direction) {
    if (direction === 1)
      return reachedMax(location.get());
    if (direction === -1)
      return reachedMin(location.get());
    return false;
  }
  function loop(direction) {
    if (!shouldLoop(direction))
      return;
    const loopDistance = contentSize * (direction * -1);
    vectors.forEach((v) => v.add(loopDistance));
  }
  const self = {
    loop
  };
  return self;
}
function ScrollProgress(limit) {
  const {
    max,
    length: scrollLength
  } = limit;
  function get(n) {
    const currentLocation = n - max;
    return currentLocation / -scrollLength;
  }
  const self = {
    get
  };
  return self;
}
function ScrollSnaps(axis, alignment, containerRect, slideRects, slideSizesWithGaps, slidesToScroll, containScroll) {
  const {
    startEdge,
    endEdge
  } = axis;
  const {
    groupSlides
  } = slidesToScroll;
  const alignments = measureSizes().map(alignment.measure);
  const snaps = measureUnaligned();
  const snapsAligned = measureAligned();
  function measureSizes() {
    return groupSlides(slideRects).map((rects) => arrayLast(rects)[endEdge] - rects[0][startEdge]).map(mathAbs);
  }
  function measureUnaligned() {
    return slideRects.map((rect) => containerRect[startEdge] - rect[startEdge]).map((snap) => -mathAbs(snap));
  }
  function measureAligned() {
    const containedStartSnap = 0;
    const containedEndSnap = arrayLast(snaps) - arrayLast(slideSizesWithGaps);
    return groupSlides(snaps).map((g) => g[0]).map((snap, index, groupedSnaps) => {
      const isFirst = !index;
      const isLast = index === arrayLastIndex(groupedSnaps);
      if (containScroll && isFirst)
        return containedStartSnap;
      if (containScroll && isLast)
        return containedEndSnap;
      return snap + alignments[index];
    });
  }
  const self = {
    snaps,
    snapsAligned
  };
  return self;
}
function ScrollTarget(loop, scrollSnaps, contentSize, limit, targetVector) {
  const {
    reachedAny,
    removeOffset,
    constrain
  } = limit;
  function minDistance(distances) {
    return distances.concat().sort((a, b) => mathAbs(a) - mathAbs(b))[0];
  }
  function findTargetSnap(target) {
    const distance = loop ? removeOffset(target) : constrain(target);
    const ascDiffsToSnaps = scrollSnaps.map((scrollSnap) => scrollSnap - distance).map((diffToSnap) => shortcut(diffToSnap, 0)).map((diff, i) => ({
      diff,
      index: i
    })).sort((d1, d2) => mathAbs(d1.diff) - mathAbs(d2.diff));
    const {
      index
    } = ascDiffsToSnaps[0];
    return {
      index,
      distance
    };
  }
  function shortcut(target, direction) {
    const targets = [target, target + contentSize, target - contentSize];
    if (!loop)
      return targets[0];
    if (!direction)
      return minDistance(targets);
    const matchingTargets = targets.filter((t) => mathSign(t) === direction);
    return minDistance(matchingTargets);
  }
  function byIndex(index, direction) {
    const diffToSnap = scrollSnaps[index] - targetVector.get();
    const distance = shortcut(diffToSnap, direction);
    return {
      index,
      distance
    };
  }
  function byDistance(distance, snap) {
    const target = targetVector.get() + distance;
    const {
      index,
      distance: targetSnapDistance
    } = findTargetSnap(target);
    const reachedBound = !loop && reachedAny(target);
    if (!snap || reachedBound)
      return {
        index,
        distance
      };
    const diffToSnap = scrollSnaps[index] - targetSnapDistance;
    const snapDistance = distance + shortcut(diffToSnap, 0);
    return {
      index,
      distance: snapDistance
    };
  }
  const self = {
    byDistance,
    byIndex,
    shortcut
  };
  return self;
}
function ScrollTo(animation, indexCurrent, indexPrevious, scrollTarget, targetVector, eventHandler) {
  function scrollTo(target) {
    const distanceDiff = target.distance;
    const indexDiff = target.index !== indexCurrent.get();
    if (distanceDiff) {
      animation.start();
      targetVector.add(distanceDiff);
    }
    if (indexDiff) {
      indexPrevious.set(indexCurrent.get());
      indexCurrent.set(target.index);
      eventHandler.emit("select");
    }
  }
  function distance(n, snap) {
    const target = scrollTarget.byDistance(n, snap);
    scrollTo(target);
  }
  function index(n, direction) {
    const targetIndex = indexCurrent.clone().set(n);
    const target = scrollTarget.byIndex(targetIndex.get(), direction);
    scrollTo(target);
  }
  const self = {
    distance,
    index
  };
  return self;
}
function Vector1D(initialValue) {
  let value = initialValue;
  function get() {
    return value;
  }
  function set(n) {
    value = normalizeInput(n);
  }
  function add(n) {
    value += normalizeInput(n);
  }
  function subtract(n) {
    value -= normalizeInput(n);
  }
  function normalizeInput(n) {
    return isNumber(n) ? n : n.get();
  }
  const self = {
    get,
    set,
    add,
    subtract
  };
  return self;
}
function Translate(axis, direction, container) {
  const translate = axis.scroll === "x" ? x : y;
  const containerStyle = container.style;
  let disabled = false;
  function x(n) {
    return `translate3d(${n}px,0px,0px)`;
  }
  function y(n) {
    return `translate3d(0px,${n}px,0px)`;
  }
  function to(target) {
    if (disabled)
      return;
    containerStyle.transform = translate(direction.apply(target));
  }
  function toggleActive(active) {
    disabled = !active;
  }
  function clear() {
    if (disabled)
      return;
    containerStyle.transform = "";
    if (!container.getAttribute("style"))
      container.removeAttribute("style");
  }
  const self = {
    clear,
    to,
    toggleActive
  };
  return self;
}
function SlideLooper(axis, direction, viewSize, contentSize, slideSizesWithGaps, scrollSnaps, slidesInView, scroll, slides) {
  const ascItems = arrayKeys(slideSizesWithGaps);
  const descItems = arrayKeys(slideSizesWithGaps).reverse();
  const loopPoints = startPoints().concat(endPoints());
  function removeSlideSizes(indexes, from) {
    return indexes.reduce((a, i) => {
      return a - slideSizesWithGaps[i];
    }, from);
  }
  function slidesInGap(indexes, gap) {
    return indexes.reduce((a, i) => {
      const remainingGap = removeSlideSizes(a, gap);
      return remainingGap > 0 ? a.concat([i]) : a;
    }, []);
  }
  function findLoopPoints(indexes, edge) {
    const isStartEdge = edge === "start";
    const offset = isStartEdge ? -contentSize : contentSize;
    const slideBounds = slidesInView.findSlideBounds([offset]);
    return indexes.map((index) => {
      const initial = isStartEdge ? 0 : -contentSize;
      const altered = isStartEdge ? contentSize : 0;
      const bounds = slideBounds.filter((b) => b.index === index)[0];
      const point = bounds[isStartEdge ? "end" : "start"];
      const location = Vector1D(-1);
      const translate = Translate(axis, direction, slides[index]);
      const target = () => scroll.get() > point ? initial : altered;
      return {
        index,
        location,
        translate,
        target
      };
    });
  }
  function startPoints() {
    const gap = scrollSnaps[0] - 1;
    const indexes = slidesInGap(descItems, gap);
    return findLoopPoints(indexes, "end");
  }
  function endPoints() {
    const gap = viewSize - scrollSnaps[0] - 1;
    const indexes = slidesInGap(ascItems, gap);
    return findLoopPoints(indexes, "start");
  }
  function canLoop() {
    return loopPoints.every(({
      index
    }) => {
      const otherIndexes = ascItems.filter((i) => i !== index);
      return removeSlideSizes(otherIndexes, viewSize) <= 0.1;
    });
  }
  function loop() {
    loopPoints.forEach((loopPoint) => {
      const {
        target,
        translate,
        location
      } = loopPoint;
      const shift = target();
      if (shift === location.get())
        return;
      translate.to(shift);
      location.set(shift);
    });
  }
  function clear() {
    loopPoints.forEach((loopPoint) => loopPoint.translate.clear());
  }
  const self = {
    canLoop,
    clear,
    loop,
    loopPoints
  };
  return self;
}
function SlidesHandler(container, eventHandler) {
  let mutationObserver;
  let destroyed = false;
  function init(emblaApi, watchSlides) {
    if (!watchSlides)
      return;
    function defaultCallback(mutations) {
      for (const mutation of mutations) {
        if (mutation.type === "childList") {
          emblaApi.reInit();
          eventHandler.emit("slidesChanged");
          break;
        }
      }
    }
    mutationObserver = new MutationObserver((mutations) => {
      if (destroyed)
        return;
      if (isBoolean(watchSlides) || watchSlides(emblaApi, mutations)) {
        defaultCallback(mutations);
      }
    });
    mutationObserver.observe(container, {
      childList: true
    });
  }
  function destroy() {
    if (mutationObserver)
      mutationObserver.disconnect();
    destroyed = true;
  }
  const self = {
    init,
    destroy
  };
  return self;
}
function SlidesInView(viewSize, contentSize, slideSizes, snaps, limit, loop, inViewThreshold) {
  const {
    removeOffset,
    constrain
  } = limit;
  const roundingSafety = 0.5;
  const cachedOffsets = loop ? [0, contentSize, -contentSize] : [0];
  const cachedBounds = findSlideBounds(cachedOffsets, inViewThreshold);
  function findSlideThresholds(threshold) {
    const slideThreshold = threshold || 0;
    return slideSizes.map((slideSize) => {
      const thresholdLimit = Limit(roundingSafety, slideSize - roundingSafety);
      return thresholdLimit.constrain(slideSize * slideThreshold);
    });
  }
  function findSlideBounds(offsets, threshold) {
    const slideOffsets = offsets || cachedOffsets;
    const slideThresholds = findSlideThresholds(threshold);
    return slideOffsets.reduce((list, offset) => {
      const bounds = snaps.map((snap, index) => ({
        start: snap - slideSizes[index] + slideThresholds[index] + offset,
        end: snap + viewSize - slideThresholds[index] + offset,
        index
      }));
      return list.concat(bounds);
    }, []);
  }
  function check(location, bounds) {
    const limitedLocation = loop ? removeOffset(location) : constrain(location);
    const slideBounds = bounds || cachedBounds;
    return slideBounds.reduce((list, slideBound) => {
      const {
        index,
        start,
        end
      } = slideBound;
      const inList = list.includes(index);
      const inView = start < limitedLocation && end > limitedLocation;
      return !inList && inView ? list.concat([index]) : list;
    }, []);
  }
  const self = {
    check,
    findSlideBounds
  };
  return self;
}
function SlideSizes(axis, containerRect, slideRects, slides, readEdgeGap, ownerWindow) {
  const {
    measureSize,
    startEdge,
    endEdge
  } = axis;
  const withEdgeGap = slideRects[0] && readEdgeGap;
  const startGap = measureStartGap();
  const endGap = measureEndGap();
  const slideSizes = slideRects.map(measureSize);
  const slideSizesWithGaps = measureWithGaps();
  function measureStartGap() {
    if (!withEdgeGap)
      return 0;
    const slideRect = slideRects[0];
    return mathAbs(containerRect[startEdge] - slideRect[startEdge]);
  }
  function measureEndGap() {
    if (!withEdgeGap)
      return 0;
    const style = ownerWindow.getComputedStyle(arrayLast(slides));
    return parseFloat(style.getPropertyValue(`margin-${endEdge}`));
  }
  function measureWithGaps() {
    return slideRects.map((rect, index, rects) => {
      const isFirst = !index;
      const isLast = index === arrayLastIndex(rects);
      if (isFirst)
        return slideSizes[index] + startGap;
      if (isLast)
        return slideSizes[index] + endGap;
      return rects[index + 1][startEdge] - rect[startEdge];
    }).map(mathAbs);
  }
  const self = {
    slideSizes,
    slideSizesWithGaps
  };
  return self;
}
function SlidesToScroll(viewSize, slideSizesWithGaps, slidesToScroll) {
  const groupByNumber = isNumber(slidesToScroll);
  function byNumber(array, groupSize) {
    return arrayKeys(array).filter((i) => i % groupSize === 0).map((i) => array.slice(i, i + groupSize));
  }
  function bySize(array) {
    return arrayKeys(array).reduce((groupSizes, i) => {
      const chunk = slideSizesWithGaps.slice(arrayLast(groupSizes), i + 1);
      const chunkSize = chunk.reduce((a, s) => a + s, 0);
      return !i || chunkSize > viewSize ? groupSizes.concat(i) : groupSizes;
    }, []).map((start, i, groupSizes) => array.slice(start, groupSizes[i + 1]));
  }
  function groupSlides(array) {
    return groupByNumber ? byNumber(array, slidesToScroll) : bySize(array);
  }
  const self = {
    groupSlides
  };
  return self;
}
function Engine(root, container, slides, ownerDocument, ownerWindow, options, eventHandler, animations) {
  const {
    align,
    axis: scrollAxis,
    direction: contentDirection,
    startIndex,
    inViewThreshold,
    loop,
    duration,
    dragFree,
    dragThreshold,
    slidesToScroll: groupSlides,
    skipSnaps,
    containScroll
  } = options;
  const containerRect = container.getBoundingClientRect();
  const slideRects = slides.map((slide) => slide.getBoundingClientRect());
  const direction = Direction(contentDirection);
  const axis = Axis(scrollAxis, contentDirection);
  const viewSize = axis.measureSize(containerRect);
  const percentOfView = PercentOfView(viewSize);
  const alignment = Alignment(align, viewSize);
  const containSnaps = !loop && !!containScroll;
  const readEdgeGap = loop || !!containScroll;
  const {
    slideSizes,
    slideSizesWithGaps
  } = SlideSizes(axis, containerRect, slideRects, slides, readEdgeGap, ownerWindow);
  const slidesToScroll = SlidesToScroll(viewSize, slideSizesWithGaps, groupSlides);
  const {
    snaps,
    snapsAligned
  } = ScrollSnaps(axis, alignment, containerRect, slideRects, slideSizesWithGaps, slidesToScroll, containSnaps);
  const contentSize = -arrayLast(snaps) + arrayLast(slideSizesWithGaps);
  const {
    snapsContained
  } = ScrollContain(viewSize, contentSize, snapsAligned, containScroll);
  const scrollSnaps = containSnaps ? snapsContained : snapsAligned;
  const {
    limit
  } = ScrollLimit(contentSize, scrollSnaps, loop);
  const index = Counter(arrayLastIndex(scrollSnaps), startIndex, loop);
  const indexPrevious = index.clone();
  const slideIndexes = arrayKeys(slides);
  const update = ({
    dragHandler,
    scrollBody: scrollBody2,
    scrollBounds,
    scrollLooper,
    slideLooper,
    eventHandler: eventHandler2,
    animation: animation2,
    options: {
      loop: loop2
    }
  }) => {
    const pointerDown = dragHandler.pointerDown();
    if (!loop2)
      scrollBounds.constrain(pointerDown);
    const hasSettled = scrollBody2.seek().settled();
    if (hasSettled && !pointerDown) {
      animation2.stop();
      eventHandler2.emit("settle");
    }
    if (!hasSettled) {
      eventHandler2.emit("scroll");
    }
    if (loop2) {
      scrollLooper.loop(scrollBody2.direction());
      slideLooper.loop();
    }
  };
  const render = ({
    scrollBody: scrollBody2,
    translate,
    location: location2
  }, lagOffset) => {
    const velocity = scrollBody2.velocity();
    const offsetLocation = location2.get() - velocity + velocity * lagOffset;
    translate.to(offsetLocation);
  };
  const animation = {
    update: () => update(engine),
    render: (lagOffset) => render(engine, lagOffset),
    start: () => animations.start(engine),
    stop: () => animations.stop(engine)
  };
  const friction = 0.68;
  const startLocation = scrollSnaps[index.get()];
  const location = Vector1D(startLocation);
  const target = Vector1D(startLocation);
  const scrollBody = ScrollBody(location, target, duration, friction);
  const scrollTarget = ScrollTarget(loop, scrollSnaps, contentSize, limit, target);
  const scrollTo = ScrollTo(animation, index, indexPrevious, scrollTarget, target, eventHandler);
  const slidesInView = SlidesInView(viewSize, contentSize, slideSizes, snaps, limit, loop, inViewThreshold);
  const engine = {
    ownerDocument,
    ownerWindow,
    eventHandler,
    containerRect,
    slideRects,
    animation,
    axis,
    direction,
    dragHandler: DragHandler(axis, direction, root, ownerDocument, ownerWindow, target, DragTracker(axis, ownerWindow), location, animation, scrollTo, scrollBody, scrollTarget, index, eventHandler, percentOfView, dragFree, dragThreshold, skipSnaps, friction),
    eventStore: EventStore(),
    percentOfView,
    index,
    indexPrevious,
    limit,
    location,
    options,
    resizeHandler: ResizeHandler(container, eventHandler, ownerWindow, slides, axis),
    scrollBody,
    scrollBounds: ScrollBounds(limit, location, target, scrollBody, percentOfView),
    scrollLooper: ScrollLooper(contentSize, limit, location, [location, target]),
    scrollProgress: ScrollProgress(limit),
    scrollSnaps,
    scrollTarget,
    scrollTo,
    slideLooper: SlideLooper(axis, direction, viewSize, contentSize, slideSizesWithGaps, scrollSnaps, slidesInView, location, slides),
    slidesHandler: SlidesHandler(container, eventHandler),
    slidesInView,
    slideIndexes,
    slidesToScroll,
    target,
    translate: Translate(axis, direction, container)
  };
  return engine;
}
function Animations(ownerWindow) {
  const timeStep = 1e3 / 60;
  let engines = [];
  let lastTimeStamp = null;
  let lag = 0;
  let animationFrame = 0;
  function animate(timeStamp) {
    if (!lastTimeStamp)
      lastTimeStamp = timeStamp;
    const elapsed = timeStamp - lastTimeStamp;
    lastTimeStamp = timeStamp;
    lag += elapsed;
    while (lag >= timeStep) {
      engines.forEach(({
        animation
      }) => animation.update());
      lag -= timeStep;
    }
    const lagOffset = mathAbs(lag / timeStep);
    engines.forEach(({
      animation
    }) => animation.render(lagOffset));
    if (animationFrame)
      ownerWindow.requestAnimationFrame(animate);
  }
  function start(engine) {
    if (!engines.includes(engine))
      engines.push(engine);
    if (animationFrame)
      return;
    animationFrame = ownerWindow.requestAnimationFrame(animate);
  }
  function stop(engine) {
    engines = engines.filter((e) => e !== engine);
    if (engines.length)
      return;
    ownerWindow.cancelAnimationFrame(animationFrame);
    lastTimeStamp = null;
    lag = 0;
    animationFrame = 0;
  }
  function reset() {
    lastTimeStamp = null;
    lag = 0;
  }
  const self = {
    start,
    stop,
    reset,
    window: ownerWindow
  };
  return self;
}
function EventHandler() {
  const listeners = {};
  let api;
  function init(emblaApi) {
    api = emblaApi;
  }
  function getListeners(evt) {
    return listeners[evt] || [];
  }
  function emit(evt) {
    getListeners(evt).forEach((e) => e(api, evt));
    return self;
  }
  function on(evt, cb) {
    listeners[evt] = getListeners(evt).concat([cb]);
    return self;
  }
  function off(evt, cb) {
    listeners[evt] = getListeners(evt).filter((e) => e !== cb);
    return self;
  }
  const self = {
    init,
    emit,
    off,
    on
  };
  return self;
}
const defaultOptions = {
  align: "center",
  axis: "x",
  container: null,
  slides: null,
  containScroll: null,
  direction: "ltr",
  slidesToScroll: 1,
  breakpoints: {},
  dragFree: false,
  dragThreshold: 10,
  inViewThreshold: 0,
  loop: false,
  skipSnaps: false,
  duration: 25,
  startIndex: 0,
  active: true,
  watchDrag: true,
  watchResize: true,
  watchSlides: true
};
function OptionsHandler(ownerWindow) {
  function mergeOptions(optionsA, optionsB) {
    return objectsMergeDeep(optionsA, optionsB || {});
  }
  function optionsAtMedia(options) {
    const optionsAtMedia2 = options.breakpoints || {};
    const matchedMediaOptions = objectKeys(optionsAtMedia2).filter((media) => ownerWindow.matchMedia(media).matches).map((media) => optionsAtMedia2[media]).reduce((a, mediaOption) => mergeOptions(a, mediaOption), {});
    return mergeOptions(options, matchedMediaOptions);
  }
  function optionsMediaQueries(optionsList) {
    return optionsList.map((options) => objectKeys(options.breakpoints || {})).reduce((acc, mediaQueries) => acc.concat(mediaQueries), []).map(ownerWindow.matchMedia);
  }
  const self = {
    mergeOptions,
    optionsAtMedia,
    optionsMediaQueries
  };
  return self;
}
function PluginsHandler(optionsHandler) {
  let activePlugins = [];
  function init(plugins, emblaApi) {
    activePlugins = plugins.filter(({
      options
    }) => optionsHandler.optionsAtMedia(options).active !== false);
    activePlugins.forEach((plugin) => plugin.init(emblaApi, optionsHandler));
    return plugins.reduce((map, plugin) => Object.assign(map, {
      [plugin.name]: plugin
    }), {});
  }
  function destroy() {
    activePlugins = activePlugins.filter((plugin) => plugin.destroy());
  }
  const self = {
    init,
    destroy
  };
  return self;
}
function EmblaCarousel(root, userOptions, userPlugins) {
  const ownerDocument = root.ownerDocument;
  const ownerWindow = ownerDocument.defaultView;
  const optionsHandler = OptionsHandler(ownerWindow);
  const pluginsHandler = PluginsHandler(optionsHandler);
  const mediaHandlers = EventStore();
  const documentVisibleHandler = EventStore();
  const eventHandler = EventHandler();
  const {
    animationRealms
  } = EmblaCarousel;
  const {
    mergeOptions,
    optionsAtMedia,
    optionsMediaQueries
  } = optionsHandler;
  const {
    on,
    off,
    emit
  } = eventHandler;
  const reInit = reActivate;
  let destroyed = false;
  let engine;
  let optionsBase = mergeOptions(defaultOptions, EmblaCarousel.globalOptions);
  let options = mergeOptions(optionsBase);
  let pluginList = [];
  let pluginApis;
  let container;
  let slides;
  function storeElements() {
    const {
      container: userContainer,
      slides: userSlides
    } = options;
    const customContainer = isString(userContainer) ? root.querySelector(userContainer) : userContainer;
    container = customContainer || root.children[0];
    const customSlides = isString(userSlides) ? container.querySelectorAll(userSlides) : userSlides;
    slides = [].slice.call(customSlides || container.children);
  }
  function activate(withOptions, withPlugins) {
    if (destroyed)
      return;
    const animationRealm = animationRealms.find((a) => a.window === ownerWindow);
    const animations = animationRealm || Animations(ownerWindow);
    if (!animationRealm)
      animationRealms.push(animations);
    optionsBase = mergeOptions(optionsBase, withOptions);
    options = optionsAtMedia(optionsBase);
    pluginList = withPlugins || pluginList;
    storeElements();
    engine = Engine(root, container, slides, ownerDocument, ownerWindow, options, eventHandler, animations);
    optionsMediaQueries([optionsBase, ...pluginList.map(({
      options: options2
    }) => options2)]).forEach((query) => mediaHandlers.add(query, "change", reActivate));
    if (!options.active)
      return;
    engine.translate.to(engine.location.get());
    engine.eventHandler.init(self);
    engine.resizeHandler.init(self, options.watchResize);
    engine.slidesHandler.init(self, options.watchSlides);
    documentVisibleHandler.add(ownerDocument, "visibilitychange", () => {
      if (ownerDocument.hidden)
        animations.reset();
    });
    if (options.loop) {
      if (!engine.slideLooper.canLoop()) {
        deActivate();
        activate({
          loop: false
        }, withPlugins);
        optionsBase = mergeOptions(optionsBase, {
          loop: true
        });
        return;
      }
      engine.slideLooper.loop();
    }
    if (container.offsetParent && slides.length) {
      engine.dragHandler.init(self, options.watchDrag);
    }
    pluginApis = pluginsHandler.init(pluginList, self);
  }
  function reActivate(withOptions, withPlugins) {
    const startIndex = selectedScrollSnap();
    deActivate();
    activate(mergeOptions({
      startIndex
    }, withOptions), withPlugins);
    eventHandler.emit("reInit");
  }
  function deActivate() {
    engine.dragHandler.destroy();
    engine.animation.stop();
    engine.eventStore.clear();
    engine.translate.clear();
    engine.slideLooper.clear();
    engine.resizeHandler.destroy();
    engine.slidesHandler.destroy();
    pluginsHandler.destroy();
    mediaHandlers.clear();
    documentVisibleHandler.clear();
  }
  function destroy() {
    if (destroyed)
      return;
    destroyed = true;
    mediaHandlers.clear();
    deActivate();
    eventHandler.emit("destroy");
  }
  function slidesInView(target) {
    const location = engine[target ? "target" : "location"].get();
    const type = options.loop ? "removeOffset" : "constrain";
    return engine.slidesInView.check(engine.limit[type](location));
  }
  function slidesNotInView(target) {
    const inView = slidesInView(target);
    return engine.slideIndexes.filter((index) => !inView.includes(index));
  }
  function scrollTo(index, jump, direction) {
    if (!options.active || destroyed)
      return;
    engine.scrollBody.useBaseFriction().useDuration(jump ? 0 : options.duration);
    engine.scrollTo.index(index, direction || 0);
  }
  function scrollNext(jump) {
    const next = engine.index.add(1).get();
    scrollTo(next, jump === true, -1);
  }
  function scrollPrev(jump) {
    const prev = engine.index.add(-1).get();
    scrollTo(prev, jump === true, 1);
  }
  function canScrollNext() {
    const next = engine.index.add(1).get();
    return next !== selectedScrollSnap();
  }
  function canScrollPrev() {
    const prev = engine.index.add(-1).get();
    return prev !== selectedScrollSnap();
  }
  function scrollSnapList() {
    return engine.scrollSnaps.map(engine.scrollProgress.get);
  }
  function scrollProgress() {
    return engine.scrollProgress.get(engine.location.get());
  }
  function selectedScrollSnap() {
    return engine.index.get();
  }
  function previousScrollSnap() {
    return engine.indexPrevious.get();
  }
  function plugins() {
    return pluginApis;
  }
  function internalEngine() {
    return engine;
  }
  function rootNode() {
    return root;
  }
  function containerNode() {
    return container;
  }
  function slideNodes() {
    return slides;
  }
  const self = {
    canScrollNext,
    canScrollPrev,
    containerNode,
    internalEngine,
    destroy,
    off,
    on,
    emit,
    plugins,
    previousScrollSnap,
    reInit,
    rootNode,
    scrollNext,
    scrollPrev,
    scrollProgress,
    scrollSnapList,
    scrollTo,
    selectedScrollSnap,
    slideNodes,
    slidesInView,
    slidesNotInView
  };
  activate(userOptions, userPlugins);
  setTimeout(() => eventHandler.emit("init"), 0);
  return self;
}
EmblaCarousel.animationRealms = [];
EmblaCarousel.globalOptions = void 0;

function emblaCarouselSvelte(emblaNode, emblaConfig = {
  options: {},
  plugins: []
}) {
  let storedEmblaConfig = emblaConfig;
  let emblaApi;
  if (canUseDOM()) {
    EmblaCarousel.globalOptions = emblaCarouselSvelte.globalOptions;
    emblaApi = EmblaCarousel(emblaNode, storedEmblaConfig.options, storedEmblaConfig.plugins);
    emblaApi.on("init", () => emblaNode.dispatchEvent(new CustomEvent("emblaInit", {
      detail: emblaApi
    })));
  }
  return {
    destroy: () => {
      if (emblaApi)
        emblaApi.destroy();
    },
    update: (newEmblaConfig) => {
      const optionsChanged = !areOptionsEqual(storedEmblaConfig.options, newEmblaConfig.options);
      const pluginsChanged = !arePluginsEqual(storedEmblaConfig.plugins, newEmblaConfig.plugins);
      if (!optionsChanged && !pluginsChanged)
        return;
      storedEmblaConfig = newEmblaConfig;
      if (emblaApi) {
        emblaApi.reInit(storedEmblaConfig.options, storedEmblaConfig.plugins);
      }
    }
  };
}
emblaCarouselSvelte.globalOptions = void 0;

const defaultOptions$1 = {
  active: true,
  breakpoints: {},
  delay: 4e3,
  jump: false,
  playOnInit: true,
  stopOnInteraction: true,
  stopOnMouseEnter: false,
  stopOnLastSnap: false,
  rootNode: null
};
function Autoplay(userOptions = {}) {
  let options;
  let emblaApi;
  let interaction;
  let timer = 0;
  let jump = false;
  function init(emblaApiInstance, optionsHandler) {
    emblaApi = emblaApiInstance;
    const {
      mergeOptions,
      optionsAtMedia
    } = optionsHandler;
    const optionsBase = mergeOptions(defaultOptions$1, Autoplay.globalOptions);
    const allOptions = mergeOptions(optionsBase, userOptions);
    options = optionsAtMedia(allOptions);
    jump = options.jump;
    interaction = options.stopOnInteraction ? destroy : stop;
    const {
      eventStore,
      ownerDocument,
      ownerWindow
    } = emblaApi.internalEngine();
    const emblaRoot = emblaApi.rootNode();
    const root = options.rootNode && options.rootNode(emblaRoot) || emblaRoot;
    emblaApi.on("pointerDown", interaction);
    if (!options.stopOnInteraction)
      emblaApi.on("pointerUp", reset);
    if (options.stopOnMouseEnter) {
      eventStore.add(root, "mouseenter", interaction);
      if (!options.stopOnInteraction)
        eventStore.add(root, "mouseleave", reset);
    }
    eventStore.add(ownerDocument, "visibilitychange", () => {
      if (ownerDocument.visibilityState === "hidden")
        return stop();
      reset();
    });
    eventStore.add(ownerWindow, "pagehide", (event) => {
      if (event.persisted)
        stop();
    });
    if (options.playOnInit)
      play();
  }
  function destroy() {
    emblaApi.off("pointerDown", interaction);
    if (!options.stopOnInteraction)
      emblaApi.off("pointerUp", reset);
    stop();
    timer = 0;
  }
  function play(jumpOverride) {
    stop();
    if (typeof jumpOverride !== "undefined")
      jump = jumpOverride;
    timer = window.setTimeout(next, options.delay);
  }
  function stop() {
    if (!timer)
      return;
    window.clearTimeout(timer);
  }
  function reset() {
    if (!timer)
      return;
    stop();
    play();
  }
  function next() {
    const {
      index
    } = emblaApi.internalEngine();
    const lastIndex = emblaApi.scrollSnapList().length - 1;
    const kill = options.stopOnLastSnap && index.get() === lastIndex;
    if (kill)
      return destroy();
    if (emblaApi.canScrollNext()) {
      emblaApi.scrollNext(jump);
    } else {
      emblaApi.scrollTo(0, jump);
    }
    play();
  }
  const self = {
    name: "autoplay",
    options: userOptions,
    init,
    destroy,
    play,
    stop,
    reset
  };
  return self;
}
Autoplay.globalOptions = void 0;

/* generated by Svelte v3.58.0 */

function get_each_context$6(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i];
	child_ctx[15] = i;
	const constants_0 = /*i*/ child_ctx[15] === /*selectedIndex*/ child_ctx[4];
	child_ctx[13] = constants_0;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[16] = list[i].image.src;
	child_ctx[17] = list[i].image.alt;
	child_ctx[18] = list[i].caption;
	return child_ctx;
}

// (111:4) {#each images as { image: {src, alt}
function create_each_block_1$1(ctx) {
	let figure;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let figcaption;
	let p;
	let t1_value = /*caption*/ ctx[18] + "";
	let t1;
	let t2;

	return {
		c() {
			figure = element("figure");
			img = element("img");
			t0 = space();
			figcaption = element("figcaption");
			p = element("p");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			figure = claim_element(nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			img = claim_element(figure_nodes, "IMG", { src: true, alt: true });
			t0 = claim_space(figure_nodes);
			figcaption = claim_element(figure_nodes, "FIGCAPTION", { class: true });
			var figcaption_nodes = children(figcaption);
			p = claim_element(figcaption_nodes, "P", { class: true });
			var p_nodes = children(p);
			t1 = claim_text(p_nodes, t1_value);
			p_nodes.forEach(detach);
			figcaption_nodes.forEach(detach);
			t2 = claim_space(figure_nodes);
			figure_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*src*/ ctx[16])) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*alt*/ ctx[17]);
			attr(p, "class", "caption svelte-362k64");
			attr(figcaption, "class", "captionWrapper svelte-362k64");
			attr(figure, "class", "imageContainer svelte-362k64");
		},
		m(target, anchor) {
			insert_hydration(target, figure, anchor);
			append_hydration(figure, img);
			append_hydration(figure, t0);
			append_hydration(figure, figcaption);
			append_hydration(figcaption, p);
			append_hydration(p, t1);
			append_hydration(figure, t2);
		},
		p(ctx, dirty) {
			if (dirty & /*images*/ 4 && !src_url_equal(img.src, img_src_value = /*src*/ ctx[16])) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*images*/ 4 && img_alt_value !== (img_alt_value = /*alt*/ ctx[17])) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*images*/ 4 && t1_value !== (t1_value = /*caption*/ ctx[18] + "")) set_data(t1, t1_value);
		},
		d(detaching) {
			if (detaching) detach(figure);
		}
	};
}

// (125:4) {#each scrollSnaps as _, i}
function create_each_block$6(ctx) {
	let li;
	let button;
	let t;
	let mounted;
	let dispose;

	function click_handler() {
		return /*click_handler*/ ctx[9](/*i*/ ctx[15]);
	}

	return {
		c() {
			li = element("li");
			button = element("button");
			t = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			button = claim_element(li_nodes, "BUTTON", { class: true });
			children(button).forEach(detach);
			t = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "class", "scrollSnapButton svelte-362k64");
			toggle_class(button, "active", /*active*/ ctx[13]);
			attr(li, "class", "scrollSnap svelte-362k64");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, button);
			append_hydration(li, t);

			if (!mounted) {
				dispose = listen(button, "click", click_handler);
				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;

			if (dirty & /*selectedIndex*/ 16) {
				toggle_class(button, "active", /*active*/ ctx[13]);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$8(ctx) {
	let div3;
	let section;
	let div2;
	let sectiontitle;
	let t0;
	let div1;
	let div0;
	let t1;
	let ul;
	let emblaCarouselSvelte_action;
	let current;
	let mounted;
	let dispose;

	sectiontitle = new Component$4({
			props: {
				title: /*title*/ ctx[0],
				subTitles: /*sub_titles*/ ctx[1]
			}
		});

	let each_value_1 = /*images*/ ctx[2];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	let each_value = /*scrollSnaps*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$6(get_each_context$6(ctx, each_value, i));
	}

	return {
		c() {
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			create_component(sectiontitle.$$.fragment);
			t0 = space();
			div1 = element("div");
			div0 = element("div");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			claim_component(sectiontitle.$$.fragment, div2_nodes);
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "slider svelte-362k64");
			attr(ul, "class", "scrollSnapContainer svelte-362k64");
			attr(div1, "class", "sliderWrapper svelte-362k64");
			attr(div2, "class", "container svelte-362k64");
			attr(section, "class", "sectionContainer svelte-362k64");
			attr(div3, "class", "section");
			attr(div3, "id", "section-96307f1f");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, section);
			append_hydration(section, div2);
			mount_component(sectiontitle, div2, null);
			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(div0, null);
				}
			}

			append_hydration(div1, t1);
			append_hydration(div1, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;

			if (!mounted) {
				dispose = [
					action_destroyer(emblaCarouselSvelte_action = emblaCarouselSvelte.call(null, div1, {
						options: /*options*/ ctx[5],
						plugins: /*plugins*/ ctx[6]
					})),
					listen(div1, "emblaInit", /*onInit*/ ctx[7])
				];

				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			const sectiontitle_changes = {};
			if (dirty & /*title*/ 1) sectiontitle_changes.title = /*title*/ ctx[0];
			if (dirty & /*sub_titles*/ 2) sectiontitle_changes.subTitles = /*sub_titles*/ ctx[1];
			sectiontitle.$set(sectiontitle_changes);

			if (dirty & /*images*/ 4) {
				each_value_1 = /*images*/ ctx[2];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1$1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(div0, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*selectedIndex, scrollTo, scrollSnaps*/ 280) {
				each_value = /*scrollSnaps*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$6(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$6(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(sectiontitle.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(sectiontitle.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_component(sectiontitle);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { sub_titles } = $$props;
	let { images } = $$props;
	let emblaApi;
	let options = { loop: true };
	let plugins = [Autoplay({ delay: 2000, stopOnInteraction: false })];
	let scrollSnaps = [];
	let selectedIndex = 0;

	function onInit(e) {
		emblaApi = e.detail;
		emblaApi.on('select', onSelect);
		$$invalidate(3, scrollSnaps = emblaApi.scrollSnapList());
	}

	function scrollTo(index) {
		emblaApi.scrollTo(index);
	}

	function onSelect(e) {
		$$invalidate(4, selectedIndex = e.selectedScrollSnap());
	}

	const click_handler = i => scrollTo(i);

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('sub_titles' in $$props) $$invalidate(1, sub_titles = $$props.sub_titles);
		if ('images' in $$props) $$invalidate(2, images = $$props.images);
	};

	return [
		title,
		sub_titles,
		images,
		scrollSnaps,
		selectedIndex,
		options,
		plugins,
		onInit,
		scrollTo,
		click_handler
	];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$7, create_fragment$8, safe_not_equal, { title: 0, sub_titles: 1, images: 2 });
	}
}

/* generated by Svelte v3.58.0 */

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, null, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$9(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let current;
	component_0 = new Component({});

	component_1 = new Component$2({
			props: {
				logo: {
					"alt": "Logo",
					"src": "https://bahygwnwefxupsynbhpc.supabase.co/storage/v1/object/public/images/6eb9dc1f-38df-458a-8366-2d737cda4d60/1687757124372logo-header.webp",
					"url": "https://bahygwnwefxupsynbhpc.supabase.co/storage/v1/object/public/images/6eb9dc1f-38df-458a-8366-2d737cda4d60/1687757124372logo-header.webp",
					"size": 2
				},
				navigations: [
					{
						"link": {
							"url": "#foundation",
							"label": "Nền Tảng Giáo Dục"
						}
					},
					{
						"link": {
							"url": "#aDayAtOurSchool",
							"label": "Một ngày tuyệt vời tại ILO"
						}
					},
					{
						"link": {
							"url": "#why",
							"label": "Vì sao chọn ILO"
						}
					}
				],
				button_text: "Đăng ký tư vấn Updated"
			}
		});

	component_2 = new Component$3({
			props: {
				sub_titles: [
					{
						"content": "VỚI CHÚNG TÔI, MỖI ĐỨA TRẺ LÀ MỘT THIÊN TÀI"
					},
					{
						"content": "Kết hợp giữa tinh hoa giáo dục Phần Lan cùng nền tảng Giáo dục Thông minh 5.0, ILO Academy mang đến cho con một môi trường hoàn thiện để phát triển toàn diện"
					}
				],
				image: {
					"alt": "Foundation",
					"src": "https://bahygwnwefxupsynbhpc.supabase.co/storage/v1/object/public/images/6eb9dc1f-38df-458a-8366-2d737cda4d60/1687767643664foundation.webp",
					"url": "https://bahygwnwefxupsynbhpc.supabase.co/storage/v1/object/public/images/6eb9dc1f-38df-458a-8366-2d737cda4d60/1687767643664foundation.webp",
					"size": 102
				},
				title: "NỀN TẢNG GIÁO DỤC CỦA ILO"
			}
		});

	component_3 = new Component$7({
			props: {
				title: "MỘT NGÀY TUYỆT VỜI TẠI ILO",
				sub_titles: [
					{
						"content": "Dựa trên nghiên cứu chuyên sâu về sự phát triển của trẻ, ILO Academy đã thiết kế thời gian biểu một ngày của con đảm bảo sự phát triển cân bằng và toàn diện cả tư duy, kiến thức - thể chất - tâm hồn. "
					},
					{
						"content": "Và đây là một ngày tuyệt vời ở ngôi trường ILO!"
					}
				],
				video: "https://ilo.edu.vn/storage/app/media/giaoducmamnon/video/ILO-videos.mp4",
				schedule: [
					{
						"data": [
							{
								"activities": [
									{ "activity": "Đón bé" },
									{ "activity": "Ăn sáng" },
									{
										"activity": "Hoạt động tập thể: trong lớp và ngoài trời"
									}
								],
								"time_range": "7:30 - 9:00"
							},
							{
								"activities": [{ "activity": "Hoạt động đầu ngày" }],
								"time_range": "9:00 - 9:30"
							},
							{
								"activities": [{ "activity": "Giờ học sáng tạo" }],
								"time_range": "9:30 - 10:00"
							},
							{
								"activities": [
									{
										"activity": "Giờ ăn xế, vệ sinh cá nhân, dọn dẹp"
									}
								],
								"time_range": "10:00 - 10:30"
							},
							{
								"activities": [{ "activity": "Vui chơi có hướng dẫn" }],
								"time_range": "10:30 – 11:00"
							},
							{
								"activities": [{ "activity": "Giờ ăn trưa" }],
								"time_range": "11:00 – 12:00"
							}
						],
						"title": "Buổi sáng",
						"iconify": {
							"icon": "ph:sun",
							"width": "72",
							"height": "70"
						}
					},
					{
						"data": [
							{
								"activities": [{ "activity": "Nghỉ trưa hoặc đọc sách" }],
								"time_range": "12:00 - 14:00"
							},
							{
								"activities": [{ "activity": "Vệ sinh cá nhân và ăn nhẹ" }],
								"time_range": "14:00 - 14:30"
							},
							{
								"activities": [{ "activity": "Hoạt động theo nhóm" }],
								"time_range": "14:30 - 15:30"
							},
							{
								"activities": [{ "activity": "Giờ học có hướng dẫn " }],
								"time_range": "15:30 - 16:30"
							},
							{
								"activities": [
									{ "activity": "Tổng kết ngày học" },
									{ "activity": "Giờ đón bé" }
								],
								"time_range": "16:30 – 17:00"
							}
						],
						"title": "Buổi chiều",
						"iconify": {
							"icon": "bi:cloud-sun",
							"width": "88",
							"height": "70"
						}
					}
				]
			}
		});

	component_4 = new Component$8({
			props: {
				title: "CƠ SỞ VẬT CHẤT ILO",
				sub_titles: [
					{
						"content": "Tuổi thơ chính là giai đoạn quan trọng nhất trong quá trình phát triển của một con người. Hiểu được điều đó, ILO đã tập trung xây dựng một môi trường học trong lành và thân thiện dành cho con để mỗi ngày tới trường đều là một ngày tràn đầy niềm vui và hạnh phúc. "
					}
				],
				images: [
					{
						"image": {
							"alt": "Sân chơi chính",
							"src": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc01.webp",
							"url": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc01.webp",
							"size": null
						},
						"caption": "Sân chơi chính"
					},
					{
						"image": {
							"alt": "Sân chơi thể thao",
							"src": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc02.webp",
							"url": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc02.webp",
							"size": null
						},
						"caption": "Sân chơi thể thao"
					},
					{
						"image": {
							"alt": "Khu vực học tập",
							"src": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc03.webp",
							"url": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc03.webp",
							"size": null
						},
						"caption": "Khu vực học tập"
					},
					{
						"image": {
							"alt": "Khu vườn ILO",
							"src": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc04.webp",
							"url": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc04.webp",
							"size": null
						},
						"caption": "Khu vườn ILO"
					},
					{
						"image": {
							"alt": "Khu vườn ILO",
							"src": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc05.webp",
							"url": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc05.webp",
							"size": null
						},
						"caption": "Khu vườn ILO"
					},
					{
						"image": {
							"alt": "Phòng tưởng tượng",
							"src": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc06.webp",
							"url": "https://ilo.edu.vn/themes/ilo/assets/landingpage/05aug/imgs/imagecompressor/csvc06.webp",
							"size": null
						},
						"caption": "Phòng tưởng tượng"
					}
				]
			}
		});

	component_5 = new Component$9({});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
		}
	};
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$9, safe_not_equal, {});
	}
}

export default Component$a;
