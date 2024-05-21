function noop() { }
const identity = x => x;
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
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
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
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
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
	let meta0;
	let meta1;
	let script0;
	let script0_src_value;
	let script1;
	let t0;
	let script2;
	let t1;
	let script3;
	let t2;
	let script4;
	let t3;
	let link0;
	let link0_href_value;
	let link1;
	let title_value;
	let meta2;
	let style;
	let t4;
	document.title = title_value = /*title*/ ctx[1];

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			script0 = element("script");
			script1 = element("script");
			t0 = text("window.dataLayer = window.dataLayer || [];\n  function gtag(){dataLayer.push(arguments);}\n  gtag('js', new Date());\n\n  gtag('config', 'G-8Q3XW1L1NY');\n  var urlObj2 = new URL(window.location.href);\n  var searchParams2 = urlObj2.searchParams;\n  window.vbt_utm_source = searchParams2.get('utm_source') || '',     \n  window.vbt_utm_medium= searchParams2.get('utm_medium') || '',     \n  window.vbt_utm_campaign= searchParams2.get('utm_campaign') || '', \n  window.vbt_utm_content = searchParams2.get('utm_content') || '',   \n  window.vbt_utm_term = searchParams2.get('utm_term') || '' \n\n \n\n");
			script2 = element("script");
			t1 = text("!function(f,b,e,v,n,t,s)\n  {if(f.fbq)return;n=f.fbq=function(){n.callMethod?\n  n.callMethod.apply(n,arguments):n.queue.push(arguments)};\n  if(!f._fbq)f._fbq=n;n.push=n;n.loaded=!0;n.version='2.0';\n  n.queue=[];t=b.createElement(e);t.async=!0;\n  t.src=v;s=b.getElementsByTagName(e)[0];\n  s.parentNode.insertBefore(t,s)}(window, document,'script',\n  'https://connect.facebook.net/en_US/fbevents.js');\n  fbq('init', '346939557913046');\n  fbq('track', 'PageView');\n");
			script3 = element("script");
			t2 = text("!function(f,b,e,v,n,t,s){if(f.fbq)return;n=f.fbq=function(){n.callMethod?n.callMethod.apply(n,arguments):n.queue.push(arguments)};if(!f._fbq)f._fbq=n;n.push=n;n.loaded=!0;n.version='2.0';n.queue=[];t=b.createElement(e);t.async=!0;t.src=v;s=b.getElementsByTagName(e)[0];s.parentNode.insertBefore(t,s)}(window,document,'script','https://connect.facebook.net/en_US/fbevents.js'); fbq('init', '330040326616650'); fbq('track', 'PageView');");
			script4 = element("script");
			t3 = text("adroll_adv_id = \"PDMI3WJZQVHGZCV3SMFR2J\";\n    adroll_pix_id = \"2JHXU5OCDRGIDAB44D3WKO\";\n    adroll_version = \"2.0\";\n\n    (function(w, d, e, o, a) {\n        w.__adroll_loaded = true;\n        w.adroll = w.adroll || [];\n        w.adroll.f = [ 'setProperties', 'identify', 'track' ];\n        var roundtripUrl = \"https://s.adroll.com/j/\" + adroll_adv_id\n                + \"/roundtrip.js\";\n        for (a = 0; a < w.adroll.f.length; a++) {\n            w.adroll[w.adroll.f[a]] = w.adroll[w.adroll.f[a]] || (function(n) {\n                return function() {\n                    w.adroll.push([ n, arguments ])\n                }\n            })(w.adroll.f[a])\n        }\n\n        e = d.createElement('script');\n        o = d.getElementsByTagName('script')[0];\n        e.async = 1;\n        e.src = roundtripUrl;\n        o.parentNode.insertBefore(e, o);\n    })(window, document);\n    adroll.track(\"pageView\");\n");
			link0 = element("link");
			link1 = element("link");
			meta2 = element("meta");
			style = element("style");
			t4 = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #004700;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #111;\n  line-height: 1.5;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.content {\n  max-width: 900px;\n  margin: 0 auto;\n  padding: 3rem 2rem;\n}\n.content p {\n    margin-bottom: 1rem;\n    line-height: 1.5;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px); /* move link back into place */\n    transition: var(--transition, 0.1s border);\n  }\n.content a.link:hover {\n      border-color: transparent;\n    }\n.content h1 {\n    font-size: 3rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n.content h2 {\n    font-size: 2.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h3 {\n    font-size: 2rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    margin-top: 1.5rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1aaxnq', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			script0 = claim_element(head_nodes, "SCRIPT", { src: true });
			var script0_nodes = children(script0);
			script0_nodes.forEach(detach);
			script1 = claim_element(head_nodes, "SCRIPT", {});
			var script1_nodes = children(script1);
			t0 = claim_text(script1_nodes, "window.dataLayer = window.dataLayer || [];\n  function gtag(){dataLayer.push(arguments);}\n  gtag('js', new Date());\n\n  gtag('config', 'G-8Q3XW1L1NY');\n  var urlObj2 = new URL(window.location.href);\n  var searchParams2 = urlObj2.searchParams;\n  window.vbt_utm_source = searchParams2.get('utm_source') || '',     \n  window.vbt_utm_medium= searchParams2.get('utm_medium') || '',     \n  window.vbt_utm_campaign= searchParams2.get('utm_campaign') || '', \n  window.vbt_utm_content = searchParams2.get('utm_content') || '',   \n  window.vbt_utm_term = searchParams2.get('utm_term') || '' \n\n \n\n");
			script1_nodes.forEach(detach);
			script2 = claim_element(head_nodes, "SCRIPT", {});
			var script2_nodes = children(script2);
			t1 = claim_text(script2_nodes, "!function(f,b,e,v,n,t,s)\n  {if(f.fbq)return;n=f.fbq=function(){n.callMethod?\n  n.callMethod.apply(n,arguments):n.queue.push(arguments)};\n  if(!f._fbq)f._fbq=n;n.push=n;n.loaded=!0;n.version='2.0';\n  n.queue=[];t=b.createElement(e);t.async=!0;\n  t.src=v;s=b.getElementsByTagName(e)[0];\n  s.parentNode.insertBefore(t,s)}(window, document,'script',\n  'https://connect.facebook.net/en_US/fbevents.js');\n  fbq('init', '346939557913046');\n  fbq('track', 'PageView');\n");
			script2_nodes.forEach(detach);
			script3 = claim_element(head_nodes, "SCRIPT", {});
			var script3_nodes = children(script3);
			t2 = claim_text(script3_nodes, "!function(f,b,e,v,n,t,s){if(f.fbq)return;n=f.fbq=function(){n.callMethod?n.callMethod.apply(n,arguments):n.queue.push(arguments)};if(!f._fbq)f._fbq=n;n.push=n;n.loaded=!0;n.version='2.0';n.queue=[];t=b.createElement(e);t.async=!0;t.src=v;s=b.getElementsByTagName(e)[0];s.parentNode.insertBefore(t,s)}(window,document,'script','https://connect.facebook.net/en_US/fbevents.js'); fbq('init', '330040326616650'); fbq('track', 'PageView');");
			script3_nodes.forEach(detach);
			script4 = claim_element(head_nodes, "SCRIPT", { type: true });
			var script4_nodes = children(script4);
			t3 = claim_text(script4_nodes, "adroll_adv_id = \"PDMI3WJZQVHGZCV3SMFR2J\";\n    adroll_pix_id = \"2JHXU5OCDRGIDAB44D3WKO\";\n    adroll_version = \"2.0\";\n\n    (function(w, d, e, o, a) {\n        w.__adroll_loaded = true;\n        w.adroll = w.adroll || [];\n        w.adroll.f = [ 'setProperties', 'identify', 'track' ];\n        var roundtripUrl = \"https://s.adroll.com/j/\" + adroll_adv_id\n                + \"/roundtrip.js\";\n        for (a = 0; a < w.adroll.f.length; a++) {\n            w.adroll[w.adroll.f[a]] = w.adroll[w.adroll.f[a]] || (function(n) {\n                return function() {\n                    w.adroll.push([ n, arguments ])\n                }\n            })(w.adroll.f[a])\n        }\n\n        e = d.createElement('script');\n        o = d.getElementsByTagName('script')[0];\n        e.async = 1;\n        e.src = roundtripUrl;\n        o.parentNode.insertBefore(e, o);\n    })(window, document);\n    adroll.track(\"pageView\");\n");
			script4_nodes.forEach(detach);

			link0 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			meta2 = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t4 = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #004700;\n\n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #111;\n  line-height: 1.5;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.content {\n  max-width: 900px;\n  margin: 0 auto;\n  padding: 3rem 2rem;\n}\n.content p {\n    margin-bottom: 1rem;\n    line-height: 1.5;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px); /* move link back into place */\n    transition: var(--transition, 0.1s border);\n  }\n.content a.link:hover {\n      border-color: transparent;\n    }\n.content h1 {\n    font-size: 3rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n.content h2 {\n    font-size: 2.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h3 {\n    font-size: 2rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    margin-top: 1.5rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			script0.async = true;
			if (!src_url_equal(script0.src, script0_src_value = "https://www.googletagmanager.com/gtag/js?id=G-8Q3XW1L1NY")) attr(script0, "src", script0_src_value);
			attr(script4, "type", "text/javascript");
			attr(link0, "rel", "icon");
			attr(link0, "type", "image/png");
			attr(link0, "sizes", "32x32");
			attr(link0, "href", link0_href_value = /*favicon*/ ctx[0].url);
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.bunny.net");
			attr(meta2, "name", "description");
			attr(meta2, "content", /*description*/ ctx[2]);
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, script0);
			append_hydration(document.head, script1);
			append_hydration(script1, t0);
			append_hydration(document.head, script2);
			append_hydration(script2, t1);
			append_hydration(document.head, script3);
			append_hydration(script3, t2);
			append_hydration(document.head, script4);
			append_hydration(script4, t3);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, meta2);
			append_hydration(document.head, style);
			append_hydration(style, t4);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link0_href_value !== (link0_href_value = /*favicon*/ ctx[0].url)) {
				attr(link0, "href", link0_href_value);
			}

			if (dirty & /*title*/ 2 && title_value !== (title_value = /*title*/ ctx[1])) {
				document.title = title_value;
			}

			if (dirty & /*description*/ 4) {
				attr(meta2, "content", /*description*/ ctx[2]);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(script0);
			detach(script1);
			detach(script2);
			detach(script3);
			detach(script4);
			detach(link0);
			detach(link1);
			detach(meta2);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
	};

	return [favicon, title, description];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

/* generated by Svelte v3.58.0 */

function create_fragment$1(ctx) {
	let t;

	return {
		c() {
			t = text("/*\n * [Package Error] \"@iconify/svelte@v4.0.2\" could not be built. \n *\n *   [1/5] Verifying package is valid…\n *   [2/5] Installing dependencies from npm…\n *   [3/5] Building package using esinstall…\n *   Running esinstall...\n *   ENOENT: no such file or directory, open '@iconify/svelte/lib/dist/functions.js'\n *   ENOENT: no such file or directory, open '/tmp/cdn/_BTFodksBdDZ1BXxNOZpr/node_modules/@iconify/svelte/lib/dist/functions.js'\n *\n * How to fix:\n *   - If you believe this to be an error in Skypack, file an issue here: https://github.com/skypackjs/skypack-cdn/issues\n *   - If you believe this to be an issue in the package, share this URL with the package authors to help them debug & fix.\n *   - Use https://skypack.dev/ to find a web-friendly alternative to find another package.\n */\n\nconsole.warn(\"[Package Error] \\\"@iconify/svelte@v4.0.2\\\" could not be built. \\n[1/5] Verifying package is valid…\\n[2/5] Installing dependencies from npm…\\n[3/5] Building package using esinstall…\\nRunning esinstall...\\nENOENT: no such file or directory, open '@iconify/svelte/lib/dist/functions.js'\\nENOENT: no such file or directory, open '/tmp/cdn/_BTFodksBdDZ1BXxNOZpr/node_modules/@iconify/svelte/lib/dist/functions.js'\");\nthrow new Error(\"[Package Error] \\\"@iconify/svelte@v4.0.2\\\" could not be built. \");\nexport default null;");
		},
		l(nodes) {
			t = claim_text(nodes, "/*\n * [Package Error] \"@iconify/svelte@v4.0.2\" could not be built. \n *\n *   [1/5] Verifying package is valid…\n *   [2/5] Installing dependencies from npm…\n *   [3/5] Building package using esinstall…\n *   Running esinstall...\n *   ENOENT: no such file or directory, open '@iconify/svelte/lib/dist/functions.js'\n *   ENOENT: no such file or directory, open '/tmp/cdn/_BTFodksBdDZ1BXxNOZpr/node_modules/@iconify/svelte/lib/dist/functions.js'\n *\n * How to fix:\n *   - If you believe this to be an error in Skypack, file an issue here: https://github.com/skypackjs/skypack-cdn/issues\n *   - If you believe this to be an issue in the package, share this URL with the package authors to help them debug & fix.\n *   - Use https://skypack.dev/ to find a web-friendly alternative to find another package.\n */\n\nconsole.warn(\"[Package Error] \\\"@iconify/svelte@v4.0.2\\\" could not be built. \\n[1/5] Verifying package is valid…\\n[2/5] Installing dependencies from npm…\\n[3/5] Building package using esinstall…\\nRunning esinstall...\\nENOENT: no such file or directory, open '@iconify/svelte/lib/dist/functions.js'\\nENOENT: no such file or directory, open '/tmp/cdn/_BTFodksBdDZ1BXxNOZpr/node_modules/@iconify/svelte/lib/dist/functions.js'\");\nthrow new Error(\"[Package Error] \\\"@iconify/svelte@v4.0.2\\\" could not be built. \");\nexport default null;");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let nav;
	let a0;
	let t0;
	let t1;
	let a1;
	let t2;
	let t3;
	let a2;
	let t4;
	let t5;
	let a3;
	let t6;
	let t7;
	let a4;
	let t8;
	let t9;
	let a5;
	let t10;
	let t11;
	let a6;
	let t12;
	let t13;
	let a7;
	let t14;
	let t15;
	let a8;
	let t16;
	let t17;
	let div;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");
			a0 = element("a");
			t0 = text("About us");
			t1 = space();
			a1 = element("a");
			t2 = text("What we do");
			t3 = space();
			a2 = element("a");
			t4 = text("Pricing");
			t5 = space();
			a3 = element("a");
			t6 = text("Book online");
			t7 = space();
			a4 = element("a");
			t8 = text("Testimonials");
			t9 = space();
			a5 = element("a");
			t10 = text("Behaviour resources");
			t11 = space();
			a6 = element("a");
			t12 = text("Blog");
			t13 = space();
			a7 = element("a");
			t14 = text("FAQ");
			t15 = space();
			a8 = element("a");
			t16 = text("Contact");
			t17 = space();
			div = element("div");
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);
			a0 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a0_nodes = children(a0);
			t0 = claim_text(a0_nodes, "About us");
			a0_nodes.forEach(detach);
			t1 = claim_space(nav_nodes);
			a1 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a1_nodes = children(a1);
			t2 = claim_text(a1_nodes, "What we do");
			a1_nodes.forEach(detach);
			t3 = claim_space(nav_nodes);
			a2 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a2_nodes = children(a2);
			t4 = claim_text(a2_nodes, "Pricing");
			a2_nodes.forEach(detach);
			t5 = claim_space(nav_nodes);
			a3 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a3_nodes = children(a3);
			t6 = claim_text(a3_nodes, "Book online");
			a3_nodes.forEach(detach);
			t7 = claim_space(nav_nodes);
			a4 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a4_nodes = children(a4);
			t8 = claim_text(a4_nodes, "Testimonials");
			a4_nodes.forEach(detach);
			t9 = claim_space(nav_nodes);
			a5 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a5_nodes = children(a5);
			t10 = claim_text(a5_nodes, "Behaviour resources");
			a5_nodes.forEach(detach);
			t11 = claim_space(nav_nodes);
			a6 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a6_nodes = children(a6);
			t12 = claim_text(a6_nodes, "Blog");
			a6_nodes.forEach(detach);
			t13 = claim_space(nav_nodes);
			a7 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a7_nodes = children(a7);
			t14 = claim_text(a7_nodes, "FAQ");
			a7_nodes.forEach(detach);
			t15 = claim_space(nav_nodes);
			a8 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a8_nodes = children(a8);
			t16 = claim_text(a8_nodes, "Contact");
			a8_nodes.forEach(detach);
			t17 = claim_space(nav_nodes);
			div = claim_element(nav_nodes, "DIV", { id: true, class: true });
			var div_nodes = children(div);
			button = claim_element(div_nodes, "BUTTON", { "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			div_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "class", "link ");
			attr(a0, "href", "/about-us");
			attr(a1, "class", "link ");
			attr(a1, "href", "/what-we-do");
			attr(a2, "class", "link ");
			attr(a2, "href", "/pricing");
			attr(a3, "class", "link ");
			attr(a3, "href", "/book");
			attr(a4, "class", "link ");
			attr(a4, "href", "/testimonials");
			attr(a5, "class", "link ");
			attr(a5, "href", "/behaviour-resources");
			attr(a6, "class", "link ");
			attr(a6, "href", "/blog");
			attr(a7, "class", "link ");
			attr(a7, "href", "/faq");
			attr(a8, "class", "link ");
			attr(a8, "href", "/contact");
			attr(button, "aria-label", "Close Navigation");
			attr(div, "id", "close");
			attr(div, "class", "svelte-3u7in3");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-3u7in3");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);
			append_hydration(nav, a0);
			append_hydration(a0, t0);
			append_hydration(nav, t1);
			append_hydration(nav, a1);
			append_hydration(a1, t2);
			append_hydration(nav, t3);
			append_hydration(nav, a2);
			append_hydration(a2, t4);
			append_hydration(nav, t5);
			append_hydration(nav, a3);
			append_hydration(a3, t6);
			append_hydration(nav, t7);
			append_hydration(nav, a4);
			append_hydration(a4, t8);
			append_hydration(nav, t9);
			append_hydration(nav, a5);
			append_hydration(a5, t10);
			append_hydration(nav, t11);
			append_hydration(nav, a6);
			append_hydration(a6, t12);
			append_hydration(nav, t13);
			append_hydration(nav, a7);
			append_hydration(a7, t14);
			append_hydration(nav, t15);
			append_hydration(nav, a8);
			append_hydration(a8, t16);
			append_hydration(nav, t17);
			append_hydration(nav, div);
			append_hydration(div, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[7]);
				mounted = true;
			}
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$2(ctx) {
	let div3;
	let div2;
	let header;
	let nav;
	let a0;
	let t0;
	let t1;
	let div0;
	let t2;
	let a1;
	let t3;
	let t4;
	let a2;
	let t5;
	let t6;
	let a3;
	let t7;
	let t8;
	let a4;
	let t9;
	let t10;
	let a5;
	let t11;
	let t12;
	let a6;
	let t13;
	let t14;
	let a7;
	let t15;
	let t16;
	let a8;
	let t17;
	let t18;
	let a9;
	let t19;
	let t20;
	let div1;
	let a10;
	let t21;
	let t22;
	let button;
	let icon;
	let t23;
	let current;
	let mounted;
	let dispose;

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block = /*mobileNavOpen*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			header = element("header");
			nav = element("nav");
			a0 = element("a");
			t0 = text("VBT");
			t1 = space();
			div0 = element("div");
			t2 = space();
			a1 = element("a");
			t3 = text("About us");
			t4 = space();
			a2 = element("a");
			t5 = text("What we do");
			t6 = space();
			a3 = element("a");
			t7 = text("Pricing");
			t8 = space();
			a4 = element("a");
			t9 = text("Book online");
			t10 = space();
			a5 = element("a");
			t11 = text("Testimonials");
			t12 = space();
			a6 = element("a");
			t13 = text("Behaviour resources");
			t14 = space();
			a7 = element("a");
			t15 = text("Blog");
			t16 = space();
			a8 = element("a");
			t17 = text("FAQ");
			t18 = space();
			a9 = element("a");
			t19 = text("Contact");
			t20 = space();
			div1 = element("div");
			a10 = element("a");
			t21 = text("VBT");
			t22 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t23 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			nav = claim_element(header_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);
			a0 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a0_nodes = children(a0);
			t0 = claim_text(a0_nodes, "VBT");
			a0_nodes.forEach(detach);
			t1 = claim_space(nav_nodes);
			div0 = claim_element(nav_nodes, "DIV", { style: true });
			children(div0).forEach(detach);
			t2 = claim_space(nav_nodes);
			a1 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a1_nodes = children(a1);
			t3 = claim_text(a1_nodes, "About us");
			a1_nodes.forEach(detach);
			t4 = claim_space(nav_nodes);
			a2 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a2_nodes = children(a2);
			t5 = claim_text(a2_nodes, "What we do");
			a2_nodes.forEach(detach);
			t6 = claim_space(nav_nodes);
			a3 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a3_nodes = children(a3);
			t7 = claim_text(a3_nodes, "Pricing");
			a3_nodes.forEach(detach);
			t8 = claim_space(nav_nodes);
			a4 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a4_nodes = children(a4);
			t9 = claim_text(a4_nodes, "Book online");
			a4_nodes.forEach(detach);
			t10 = claim_space(nav_nodes);
			a5 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a5_nodes = children(a5);
			t11 = claim_text(a5_nodes, "Testimonials");
			a5_nodes.forEach(detach);
			t12 = claim_space(nav_nodes);
			a6 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a6_nodes = children(a6);
			t13 = claim_text(a6_nodes, "Behaviour resources");
			a6_nodes.forEach(detach);
			t14 = claim_space(nav_nodes);
			a7 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a7_nodes = children(a7);
			t15 = claim_text(a7_nodes, "Blog");
			a7_nodes.forEach(detach);
			t16 = claim_space(nav_nodes);
			a8 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a8_nodes = children(a8);
			t17 = claim_text(a8_nodes, "FAQ");
			a8_nodes.forEach(detach);
			t18 = claim_space(nav_nodes);
			a9 = claim_element(nav_nodes, "A", { class: true, href: true });
			var a9_nodes = children(a9);
			t19 = claim_text(a9_nodes, "Contact");
			a9_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			t20 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a10 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a10_nodes = children(a10);
			t21 = claim_text(a10_nodes, "VBT");
			a10_nodes.forEach(detach);
			t22 = claim_space(div1_nodes);

			button = claim_element(div1_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t23 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "class", "link  svelte-3u7in3");
			attr(a0, "href", "/");
			set_style(div0, "flex", "1");
			attr(a1, "class", "link  svelte-3u7in3");
			attr(a1, "href", "/about-us");
			attr(a2, "class", "link  svelte-3u7in3");
			attr(a2, "href", "/what-we-do");
			attr(a3, "class", "link  svelte-3u7in3");
			attr(a3, "href", "/pricing");
			attr(a4, "class", "link  svelte-3u7in3");
			attr(a4, "href", "/book");
			attr(a5, "class", "link  svelte-3u7in3");
			attr(a5, "href", "/testimonials");
			attr(a6, "class", "link  svelte-3u7in3");
			attr(a6, "href", "/behaviour-resources");
			attr(a7, "class", "link  svelte-3u7in3");
			attr(a7, "href", "/blog");
			attr(a8, "class", "link  svelte-3u7in3");
			attr(a8, "href", "/faq");
			attr(a9, "class", "link  svelte-3u7in3");
			attr(a9, "href", "/contact");
			attr(nav, "class", "desktop-nav menu-links svelte-3u7in3");
			attr(a10, "href", "/");
			attr(a10, "class", "logo svelte-3u7in3");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(button, "class", "svelte-3u7in3");
			attr(div1, "class", "mobile-nav svelte-3u7in3");
			attr(header, "class", "section-container svelte-3u7in3");
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-e2e28b90-f327-46d1-bfa6-58acda68a12c");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, header);
			append_hydration(header, nav);
			append_hydration(nav, a0);
			append_hydration(a0, t0);
			append_hydration(nav, t1);
			append_hydration(nav, div0);
			append_hydration(nav, t2);
			append_hydration(nav, a1);
			append_hydration(a1, t3);
			append_hydration(nav, t4);
			append_hydration(nav, a2);
			append_hydration(a2, t5);
			append_hydration(nav, t6);
			append_hydration(nav, a3);
			append_hydration(a3, t7);
			append_hydration(nav, t8);
			append_hydration(nav, a4);
			append_hydration(a4, t9);
			append_hydration(nav, t10);
			append_hydration(nav, a5);
			append_hydration(a5, t11);
			append_hydration(nav, t12);
			append_hydration(nav, a6);
			append_hydration(a6, t13);
			append_hydration(nav, t14);
			append_hydration(nav, a7);
			append_hydration(a7, t15);
			append_hydration(nav, t16);
			append_hydration(nav, a8);
			append_hydration(a8, t17);
			append_hydration(nav, t18);
			append_hydration(nav, a9);
			append_hydration(a9, t19);
			append_hydration(header, t20);
			append_hydration(header, div1);
			append_hydration(div1, a10);
			append_hydration(a10, t21);
			append_hydration(div1, t22);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t23);
			if (if_block) if_block.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (/*mobileNavOpen*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 1) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div1, null);
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
			transition_in(icon.$$.fragment, local);
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_component(icon);
			if (if_block) if_block.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(0, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(0, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(1, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('description' in $$props) $$invalidate(3, description = $$props.description);
		if ('logo' in $$props) $$invalidate(4, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(5, site_nav = $$props.site_nav);
	};

	return [
		mobileNavOpen,
		favicon,
		title,
		description,
		logo,
		site_nav,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$1, create_fragment$2, safe_not_equal, {
			favicon: 1,
			title: 2,
			description: 3,
			logo: 4,
			site_nav: 5
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$3(ctx) {
	let div3;
	let div2;
	let header;
	let div0;
	let t0;
	let div1;
	let h1;
	let t1;
	let header_aria_label_value;

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			header = element("header");
			div0 = element("div");
			t0 = space();
			div1 = element("div");
			h1 = element("h1");
			t1 = text(/*headline*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);

			header = claim_element(div2_nodes, "HEADER", {
				style: true,
				role: true,
				"aria-label": true,
				class: true
			});

			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t0 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h1 = claim_element(div1_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t1 = claim_text(h1_nodes, /*headline*/ ctx[1]);
			h1_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container svelte-1643yvf");
			attr(h1, "class", "headline svelte-1643yvf");
			attr(div1, "class", "section-container svelte-1643yvf");
			set_style(header, "background-image", "url('" + /*background*/ ctx[0].url + "')");
			attr(header, "role", "img");
			attr(header, "aria-label", header_aria_label_value = /*background*/ ctx[0].alt);
			attr(header, "class", "svelte-1643yvf");
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-d2a63952-bdac-461d-b42c-33ea775a244c");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, header);
			append_hydration(header, div0);
			append_hydration(header, t0);
			append_hydration(header, div1);
			append_hydration(div1, h1);
			append_hydration(h1, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*headline*/ 2) set_data(t1, /*headline*/ ctx[1]);

			if (dirty & /*background*/ 1) {
				set_style(header, "background-image", "url('" + /*background*/ ctx[0].url + "')");
			}

			if (dirty & /*background*/ 1 && header_aria_label_value !== (header_aria_label_value = /*background*/ ctx[0].alt)) {
				attr(header, "aria-label", header_aria_label_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { background } = $$props;
	let { headline } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('background' in $$props) $$invalidate(0, background = $$props.background);
		if ('headline' in $$props) $$invalidate(1, headline = $$props.headline);
		if ('logo' in $$props) $$invalidate(5, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(6, site_nav = $$props.site_nav);
	};

	return [background, headline, favicon, title, description, logo, site_nav];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$3, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			background: 0,
			headline: 1,
			logo: 5,
			site_nav: 6
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i];
	child_ctx[8] = i;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].item;
	child_ctx[10] = list[i].icon;
	child_ctx[12] = i;
	return child_ctx;
}

// (111:10) {#each tier.features as { item, icon }
function create_each_block_1(ctx) {
	let li;
	let span0;
	let icon;
	let t0;
	let span1;
	let t1_value = /*item*/ ctx[9] + "";
	let t1;
	let t2;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[10] } });

	return {
		c() {
			li = element("li");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			span1 = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			span0 = claim_element(li_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(li_nodes);
			span1 = claim_element(li_nodes, "SPAN", {});
			var span1_nodes = children(span1);
			t1 = claim_text(span1_nodes, t1_value);
			span1_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "icon svelte-2w0b9m");
			attr(li, "class", "svelte-2w0b9m");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span0);
			mount_component(icon, span0, null);
			append_hydration(li, t0);
			append_hydration(li, span1);
			append_hydration(span1, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*tiers*/ 4) icon_changes.icon = /*icon*/ ctx[10];
			icon.$set(icon_changes);
			if ((!current || dirty & /*tiers*/ 4) && t1_value !== (t1_value = /*item*/ ctx[9] + "")) set_data(t1, t1_value);
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
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

// (120:8) {#if tier.link.label}
function create_if_block$1(ctx) {
	let a;
	let t_value = /*tier*/ ctx[6].link.label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*tier*/ ctx[6].link.url);
			attr(a, "class", "button svelte-2w0b9m");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*tiers*/ 4 && t_value !== (t_value = /*tier*/ ctx[6].link.label + "")) set_data(t, t_value);

			if (dirty & /*tiers*/ 4 && a_href_value !== (a_href_value = /*tier*/ ctx[6].link.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (99:4) {#each tiers as tier, tier_index}
function create_each_block(ctx) {
	let div1;
	let header;
	let h3;
	let t0_value = /*tier*/ ctx[6].title + "";
	let t0;
	let t1;
	let div0;
	let span0;
	let t2_value = /*tier*/ ctx[6].price.numerator + "";
	let t2;
	let t3;
	let span1;
	let t4_value = /*tier*/ ctx[6].price.denominator + "";
	let t4;
	let t5;
	let span2;
	let raw_value = /*tier*/ ctx[6].description.html + "";
	let t6;
	let hr;
	let t7;
	let ul;
	let t8;
	let t9;
	let current;
	let each_value_1 = /*tier*/ ctx[6].features;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	let if_block = /*tier*/ ctx[6].link.label && create_if_block$1(ctx);

	return {
		c() {
			div1 = element("div");
			header = element("header");
			h3 = element("h3");
			t0 = text(t0_value);
			t1 = space();
			div0 = element("div");
			span0 = element("span");
			t2 = text(t2_value);
			t3 = space();
			span1 = element("span");
			t4 = text(t4_value);
			t5 = space();
			span2 = element("span");
			t6 = space();
			hr = element("hr");
			t7 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t8 = space();
			if (if_block) if_block.c();
			t9 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			header = claim_element(div1_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			h3 = claim_element(header_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, t0_value);
			h3_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t2 = claim_text(span0_nodes, t2_value);
			span0_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t4 = claim_text(span1_nodes, t4_value);
			span1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(header_nodes);
			span2 = claim_element(header_nodes, "SPAN", { class: true });
			var span2_nodes = children(span2);
			span2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t6 = claim_space(div1_nodes);
			hr = claim_element(div1_nodes, "HR", { class: true });
			t7 = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t8 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			t9 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "title svelte-2w0b9m");
			attr(span0, "class", "numerator svelte-2w0b9m");
			attr(span1, "class", "denominator svelte-2w0b9m");
			attr(div0, "class", "price svelte-2w0b9m");
			attr(span2, "class", "description");
			attr(header, "class", "svelte-2w0b9m");
			attr(hr, "class", "svelte-2w0b9m");
			attr(ul, "class", "features svelte-2w0b9m");
			attr(div1, "class", "tier svelte-2w0b9m");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, header);
			append_hydration(header, h3);
			append_hydration(h3, t0);
			append_hydration(header, t1);
			append_hydration(header, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t2);
			append_hydration(div0, t3);
			append_hydration(div0, span1);
			append_hydration(span1, t4);
			append_hydration(header, t5);
			append_hydration(header, span2);
			span2.innerHTML = raw_value;
			append_hydration(div1, t6);
			append_hydration(div1, hr);
			append_hydration(div1, t7);
			append_hydration(div1, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(div1, t8);
			if (if_block) if_block.m(div1, null);
			append_hydration(div1, t9);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*tiers*/ 4) && t0_value !== (t0_value = /*tier*/ ctx[6].title + "")) set_data(t0, t0_value);
			if ((!current || dirty & /*tiers*/ 4) && t2_value !== (t2_value = /*tier*/ ctx[6].price.numerator + "")) set_data(t2, t2_value);
			if ((!current || dirty & /*tiers*/ 4) && t4_value !== (t4_value = /*tier*/ ctx[6].price.denominator + "")) set_data(t4, t4_value);
			if ((!current || dirty & /*tiers*/ 4) && raw_value !== (raw_value = /*tier*/ ctx[6].description.html + "")) span2.innerHTML = raw_value;
			if (dirty & /*tiers*/ 4) {
				each_value_1 = /*tier*/ ctx[6].features;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (/*tier*/ ctx[6].link.label) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					if_block.m(div1, t9);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
			if (if_block) if_block.d();
		}
	};
}

function create_fragment$4(ctx) {
	let div2;
	let div1;
	let section;
	let h2;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let div0;
	let current;
	let each_value = /*tiers*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			h3 = element("h3");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			h3 = claim_element(section_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*subheading*/ ctx[1]);
			h3_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-2w0b9m");
			attr(h3, "class", "subheading svelte-2w0b9m");
			attr(div0, "class", "tiers svelte-2w0b9m");
			attr(section, "class", "section-container svelte-2w0b9m");
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-cd67eb14-1ece-4ff6-9d59-ee163a18c062");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, h3);
			append_hydration(h3, t2);
			append_hydration(section, t3);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div0, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (!current || dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (dirty & /*tiers*/ 4) {
				each_value = /*tiers*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div0, null);
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

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { tiers } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('description' in $$props) $$invalidate(5, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('tiers' in $$props) $$invalidate(2, tiers = $$props.tiers);
	};

	return [heading, subheading, tiers, favicon, title, description];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$4, safe_not_equal, {
			favicon: 3,
			title: 4,
			description: 5,
			heading: 0,
			subheading: 1,
			tiers: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i].title;
	child_ctx[5] = list[i].links;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (66:12) {#each links as { link }}
function create_each_block_1$1(ctx) {
	let li;
	let a;
	let t0_value = /*link*/ ctx[8].label + "";
	let t0;
	let a_href_value;
	let t1;

	return {
		c() {
			li = element("li");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-u1zmy0");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t0);
			append_hydration(li, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*menus*/ 2 && t0_value !== (t0_value = /*link*/ ctx[8].label + "")) set_data(t0, t0_value);

			if (dirty & /*menus*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (62:6) {#each menus as { title, links }}
function create_each_block$1(ctx) {
	let nav;
	let h3;
	let t0_value = /*title*/ ctx[2] + "";
	let t0;
	let t1;
	let ul;
	let t2;
	let each_value_1 = /*links*/ ctx[5];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	return {
		c() {
			nav = element("nav");
			h3 = element("h3");
			t0 = text(t0_value);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", {});
			var nav_nodes = children(nav);
			h3 = claim_element(nav_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, t0_value);
			h3_nodes.forEach(detach);
			t1 = claim_space(nav_nodes);
			ul = claim_element(nav_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t2 = claim_space(nav_nodes);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-u1zmy0");
			attr(ul, "class", "svelte-u1zmy0");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);
			append_hydration(nav, h3);
			append_hydration(h3, t0);
			append_hydration(nav, t1);
			append_hydration(nav, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(nav, t2);
		},
		p(ctx, dirty) {
			if (dirty & /*menus*/ 2 && t0_value !== (t0_value = /*title*/ ctx[2] + "")) set_data(t0, t0_value);

			if (dirty & /*menus*/ 2) {
				each_value_1 = /*links*/ ctx[5];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
		}
	};
}

function create_fragment$5(ctx) {
	let div4;
	let div3;
	let footer;
	let div2;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";
	let t;
	let div1;
	let each_value = /*menus*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			footer = element("footer");
			div2 = element("div");
			div0 = element("div");
			t = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			footer = claim_element(div3_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div2 = claim_element(footer_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "content svelte-u1zmy0");
			attr(div1, "class", "nav-items svelte-u1zmy0");
			attr(div2, "class", "section-container svelte-u1zmy0");
			attr(footer, "class", "svelte-u1zmy0");
			attr(div3, "class", "component");
			attr(div4, "class", "section");
			attr(div4, "id", "section-68a8b55d-acfa-486d-a83d-e69ed7eed0e3");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, footer);
			append_hydration(footer, div2);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*menus*/ 2) {
				each_value = /*menus*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div1, null);
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
			if (detaching) detach(div4);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { content } = $$props;
	let { menus } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(2, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
		if ('menus' in $$props) $$invalidate(1, menus = $$props.menus);
	};

	return [content, menus, title, favicon, description];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$5, safe_not_equal, {
			favicon: 3,
			title: 2,
			description: 4,
			content: 0,
			menus: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
	};

	return [favicon, title, description];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$5, null, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
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

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "",
					"src": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"url": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"size": 1
				},
				title: "Pricing",
				description: "Experience comprehensive and personalised care for your pet. Our commitment to your pet's well-being and mental health goes beyond a single consultation."
			}
		});

	component_1 = new Component$2({
			props: {
				favicon: {
					"alt": "",
					"src": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"url": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"size": 1
				},
				title: "Pricing",
				description: "Experience comprehensive and personalised care for your pet. Our commitment to your pet's well-being and mental health goes beyond a single consultation.",
				logo: {
					"image": {
						"alt": "",
						"src": "https://jbbjtodsvhsgjappwopg.supabase.co/storage/v1/object/public/sites/public-library/assets/logoipsum-261 (1).svg",
						"url": "https://jbbjtodsvhsgjappwopg.supabase.co/storage/v1/object/public/sites/public-library/assets/logoipsum-261 (1).svg",
						"size": 3
					},
					"title": "Vet Behaviour Team"
				},
				site_nav: [
					{
						"link": {
							"url": "",
							"label": "Home",
							"active": false
						}
					},
					{ "link": { "url": "/", "label": "About" } },
					{
						"link": {
							"url": "https://primosites.vercel.app/primo-library",
							"label": "Contact"
						}
					}
				]
			}
		});

	component_2 = new Component$3({
			props: {
				favicon: {
					"alt": "",
					"src": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"url": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"size": 1
				},
				title: "Pricing",
				description: "Experience comprehensive and personalised care for your pet. Our commitment to your pet's well-being and mental health goes beyond a single consultation.",
				background: {
					"alt": "",
					"src": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1686749422842pexels-countrykcom-1195975wide.jpg",
					"url": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1686749422842pexels-countrykcom-1195975wide.jpg",
					"size": 461
				},
				headline: "",
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "Vet Behaviour Team"
				},
				site_nav: [
					{
						"link": {
							"url": "/about-us",
							"label": "About us",
							"active": false
						}
					},
					{
						"link": {
							"url": "/what-we-do",
							"label": "What we do",
							"active": false
						}
					},
					{
						"link": { "url": "/book", "label": "Book online" }
					},
					{
						"link": { "url": "/blog", "label": "Blog" }
					},
					{
						"link": {
							"url": "/testimonials",
							"label": "Testimonials"
						}
					},
					{
						"link": { "url": "/contact", "label": "Contact us" }
					},
					{
						"link": {
							"url": "/behaviour-resources",
							"label": "Behaviour Resources"
						}
					},
					{
						"link": { "url": "/faq", "label": "FAQ" }
					}
				]
			}
		});

	component_3 = new Component$4({
			props: {
				favicon: {
					"alt": "",
					"src": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"url": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"size": 1
				},
				title: "Pricing",
				description: "Experience comprehensive and personalised care for your pet. Our commitment to your pet's well-being and mental health goes beyond a single consultation.",
				heading: "Pricing",
				subheading: "Experience comprehensive and personalised care for your pet. Our commitment to your pet's well-being and mental health goes beyond a single consultation.",
				tiers: [
					{
						"link": { "url": "/book", "label": "Book now" },
						"price": {
							"numerator": "$695",
							"denominator": "for single pet (canine or feline)"
						},
						"title": "Initial behaviour consult",
						"features": [
							{
								"icon": "Lorem elit et",
								"item": "- 2 hour house call"
							},
							{
								"icon": "Amet aliqua enim",
								"item": "- behavioural diagnosis and tailored therapeutic plan"
							},
							{
								"icon": "Laboris qui lorem",
								"item": "- travel within the Sydney metro area (30km from CBD)"
							},
							{
								"icon": "- liaison with your regular GP veterinarian and behavioural trainer",
								"item": "- veterinary behaviour report"
							},
							{
								"icon": "",
								"item": "- 8 weeks email support"
							},
							{
								"icon": "- for 30-50km beyond Sydney CBD - $50 travel surcharge",
								"item": " For consultations outside the Sydney Metro area the following travel fees apply "
							},
							{
								"icon": "Reprehenderit ex enim",
								"item": "- for 30-50km beyond Sydney CBD - $50 travel surcharge"
							},
							{
								"icon": "",
								"item": "- for 50-100km beyond Sydney CBD - $100 travel surcharge"
							}
						],
						"description": {
							"html": "<p>During the initial consultation, we take the time to understand your unique situation and develop a deep understanding of your pet's behaviour. Our expert team will explain the underlying causes of your pet's behaviour and provide clear explanations of our recommended treatment options. We believe in empowering you with knowledge, so you can make informed decisions for your pet.</p>\n<p><b> There is a non-refundable deposit of $100.00 to secure your booking.</b></p>",
							"markdown": "During the initial consultation, we take the time to understand your unique situation and develop a deep understanding of your pet's behaviour. Our expert team will explain the underlying causes of your pet's behaviour and provide clear explanations of our recommended treatment options. We believe in empowering you with knowledge, so you can make informed decisions for your pet.\n\n\n<b> There is a non-refundable deposit of $100.00 to secure your booking.</b>\n\n"
						}
					}
				]
			}
		});

	component_4 = new Component$5({
			props: {
				favicon: {
					"alt": "",
					"src": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"url": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"size": 1
				},
				title: "Pricing",
				description: "Experience comprehensive and personalised care for your pet. Our commitment to your pet's well-being and mental health goes beyond a single consultation.",
				content: {
					"html": "<p><em>Working Sydney Wide & Online</em></p>\n<p>Vet Behaviour Team <br>\n0432 881 174</p>\n<p>ABN: 34603289176 copyright© Vet Behaviour Team PTY LTD 2023</p>\n<p><a href=\"https://storage.googleapis.com/tour-nament.appspot.com/media/Vet%20Behaviour%20Team%20Terms%20and%20Conditions.pdf\" download style=\"font-weight:bold;font-size:14px;\">TERMS AND CONDITIONS</a></p>\n<p><font size=\"2\">Vet Behaviour Team acknowledges the Traditional Custodians of country throughout Australia and their connections to land, sea and community. We pay our respect to their Elders past and present, and extend that respect to all Aboriginal and Torres Strait Islander peoples today.</font></p>",
					"markdown": "*Working Sydney Wide & Online*\n\nVet Behaviour Team <br>\n0432 881 174\n\nABN: 34603289176 copyright© Vet Behaviour Team PTY LTD 2023\n\n<a href=\"https://storage.googleapis.com/tour-nament.appspot.com/media/Vet%20Behaviour%20Team%20Terms%20and%20Conditions.pdf\" download style=\"font-weight:bold;font-size:14px;\">TERMS AND CONDITIONS</a>\n\n<font size=\"2\">Vet Behaviour Team acknowledges the Traditional Custodians of country throughout Australia and their connections to land, sea and community. We pay our respect to their Elders past and present, and extend that respect to all Aboriginal and Torres Strait Islander peoples today.</font>\n\n"
				},
				menus: []
			}
		});

	component_5 = new Component$6({
			props: {
				favicon: {
					"alt": "",
					"src": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"url": "https://cecahqcvnivcvvvhsdfd.supabase.co/storage/v1/object/public/images/5cfeba61-0502-41db-b62b-2bdd3a76f0b6/1688236910000icons8-dog-heart-ios-16-glyph-32.png",
					"size": 1
				},
				title: "Pricing",
				description: "Experience comprehensive and personalised care for your pet. Our commitment to your pet's well-being and mental health goes beyond a single consultation."
			}
		});

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

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$6, safe_not_equal, {});
	}
}

export default Component$7;
