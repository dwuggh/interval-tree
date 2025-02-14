use std::cmp::Ordering;
use std::fmt::Debug;
pub mod range;
pub use range::TextRange;

fn safe_mut<'a, T>(n: *mut T) -> &'a mut T {
    unsafe { n.as_mut().unwrap() }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Color {
    Red = 0,
    Black,
}

impl Color {
    pub fn flip(&self) -> Color {
        match self {
            Color::Red => Color::Black,
            Color::Black => Color::Red,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Node<T: Clone + Debug> {
    pub key: TextRange,
    pub val: T,
    left: MaybeNode<T>,
    right: MaybeNode<T>,
    color: Color,
    parent: *mut Node<T>,
    is_right_child: bool,
    n: usize,
}
pub type BoxedNode<T> = Box<Node<T>>;
pub type MaybeNode<T> = Option<BoxedNode<T>>;

impl<T: Clone + Debug> Node<T> {
    #[inline]
    pub fn red(node: &MaybeNode<T>) -> bool {
        node.as_ref()
            .map(|n| n.color == Color::Red)
            .unwrap_or(false)
    }

    #[inline]
    pub fn new(key: TextRange, val: T) -> Self {
        Self::new_with_parent(key, val, std::ptr::null_mut(), false)
    }

    #[inline]
    pub fn new_with_parent(
        key: TextRange,
        val: T,
        parent: *mut Node<T>,
        is_right_child: bool,
    ) -> Node<T> {
        Self {
            key,
            val,
            left: None,
            right: None,
            color: Color::Red,
            n: 1,
            parent,
            is_right_child,
        }
    }

    #[inline]
    pub fn new_boxed(key: TextRange, val: T) -> BoxedNode<T> {
        Box::new(Self::new(key, val))
    }

    #[inline]
    pub fn new_boxed_with_parent(
        key: TextRange,
        val: T,
        parent: *mut Node<T>,
        is_right_child: bool,
    ) -> BoxedNode<T> {
        Box::new(Self::new_with_parent(key, val, parent, is_right_child))
    }

    #[inline]
    pub fn set_parent(&mut self, parent: &mut Node<T>) {
        self.parent = parent
    }

    /// perform the following operation, \\ is the red link:
    ///      |            |
    ///      n            x
    ///     / \\        // \
    ///        x    =>  n
    ///       / \      / \
    ///      c            c
    pub fn rotate_left<'a>(node: &'a mut BoxedNode<T>) -> Option<&'a mut BoxedNode<T>> {
        let mut x = node.right.take()?;
        let mut c = x.left.take();
        if let Some(ref mut c) = c {
            c.parent = node.as_mut();
            c.is_right_child = true;
        }
        node.right = c;
        x.color = node.color;
        x.parent = node.parent;
        x.is_right_child = node.is_right_child;
        node.parent = x.as_mut();
        node.is_right_child = false;
        x.n = node.n;
        node.color = Color::Red;
        node.n = node.n();
        // node and x swapped content
        std::mem::swap(node, &mut x);
        node.left.replace(x);
        Some(node)
    }

    /// perform the following operation, \\ is the red link:
    ///      |            |
    ///      n            x
    ///    // \          / \\
    ///    x       =>       n
    ///   / \              / \
    ///      c            c
    pub fn rotate_right<'a>(node: &'a mut BoxedNode<T>) -> Option<&'a mut BoxedNode<T>> {
        let mut x = node.left.take()?;
        let mut c = x.right.take();
        if let Some(ref mut c) = c {
            c.parent = node.as_mut();
            c.is_right_child = false;
        }
        node.left = c;
        x.color = node.color;
        x.parent = node.parent;
        x.is_right_child = node.is_right_child;
        node.parent = x.as_mut();
        node.is_right_child = true;
        node.color = Color::Red;
        x.n = node.n;
        node.n = node.n();

        std::mem::swap(node, &mut x);
        node.right.replace(x);
        Some(node)
    }

    /// total number of items in this sub-tree
    #[inline]
    pub fn n(&self) -> usize {
        let l = match self.left {
            Some(ref n) => n.n,
            None => 0,
        };
        let r = match self.right {
            Some(ref n) => n.n,
            None => 0,
        };
        1 + l + r
    }

    fn min(&self) -> &Node<T> {
        if let Some(ref l) = self.left {
            l.min()
        } else {
            self
        }
    }

    fn min_mut<'a>(&'a mut self) -> &'a mut Node<T> {
        if let Some(ref mut l) = self.left {
            l.min_mut()
        } else {
            self
        }
    }

    #[inline]
    fn parent(&self) -> Option<&Node<T>> {
        unsafe { self.parent.as_ref() }
    }

    #[inline]
    fn parent_mut(&self) -> Option<&mut Node<T>> {
        unsafe { self.parent.as_mut() }
    }

    fn get(&self, key: TextRange) -> Option<T> {
        match key.cmp(&self.key) {
            std::cmp::Ordering::Equal => Some(self.val.clone()), // TODO determine clone here
            std::cmp::Ordering::Less => self.left.as_ref().and_then(|n| n.get(key)),
            std::cmp::Ordering::Greater => self.right.as_ref().and_then(|n| n.get(key)),
        }
    }
}

impl<T: Clone + Debug> Node<T> {
    pub fn insert_at<'a, F: Fn(T, T) -> anyhow::Result<(T, bool)>>(
        node: &'a mut MaybeNode<T>,
        key: TextRange,
        val: T,
        parent: *mut Node<T>,
        is_right_child: bool,
        merge: &F,
    ) -> Option<&'a mut BoxedNode<T>> {
        match node {
            Some(ref mut n) => Node::insert_at_inner(n, key, val, merge),
            None => {
                node.replace(Node::new_boxed_with_parent(
                    key,
                    val.clone(),
                    parent,
                    is_right_child,
                ));
                node.as_mut()
            }
        }
    }

    fn insert_at_inner<'a, F: Fn(T, T) -> anyhow::Result<(T, bool)>>(
        node: &'a mut BoxedNode<T>,
        mut key: TextRange,
        val: T,
        merge: &F,
    ) -> Option<&'a mut BoxedNode<T>> {
        let intersect = key.intersects(node.key);
        // TODO too taunting, also, plist should be cloned?
        let ptr: *mut Node<T> = node.as_mut();
        if intersect {
            if key.start < node.key.start {
                let key_left = key.split_at(node.key.start, true);
                Node::insert_at(&mut node.left, key_left, val.clone(), ptr, false, merge);

                if key.end < node.key.end {
                    let key_right = node.key.split_at(key.end, false);
                    Node::insert_at(
                        &mut node.right,
                        key_right,
                        node.val.clone(),
                        ptr,
                        true,
                        merge,
                    );
                } else if key.end > node.key.end {
                    let key_right = key.split_at(node.key.end, false);
                    Node::insert_at(&mut node.right, key_right, val.clone(), ptr, true, merge);
                }
            } else {
                let key_left = node.key.split_at(key.start, true);
                Node::insert_at(
                    &mut node.left,
                    key_left,
                    node.val.clone(),
                    ptr,
                    false,
                    merge,
                );

                if key.end < node.key.end {
                    let key_right = node.key.split_at(key.end, false);
                    Node::insert_at(
                        &mut node.right,
                        key_right,
                        node.val.clone(),
                        ptr,
                        true,
                        merge,
                    );
                } else if key.end > node.key.end {
                    let key_right = key.split_at(node.key.end, false);
                    Node::insert_at(&mut node.right, key_right, val.clone(), ptr, true, merge);
                }
            }
        }
        let cmp = key.cmp(&node.key);
        match cmp {
            Ordering::Less => {
                Node::insert_at(&mut node.left, key, val, ptr, false, merge)?;
            }
            Ordering::Equal => {
                // let (val, changed) = add_properties(
                //     val,
                //     node.val,
                //     crate::textprops::PropertySetType::Replace,
                //     false,
                //
                // )
                // .ok()?;
                let (val, changed) = merge(val, node.val.clone()).ok()?;
                if changed {
                    node.val = val;
                }
            }
            Ordering::Greater => {
                Node::insert_at(&mut node.right, key, val, ptr, true, merge)?;
            }
        };

        // cond1: r_red && !l_red
        if Node::red(&node.right) && !Node::red(&node.left) {
            Node::rotate_left(node)?;
        }

        // cond2: l_red && ll_red
        let cond2 = match node.left {
            Some(ref nl) => nl.color == Color::Red && Node::red(&nl.left),
            None => false,
        };
        if cond2 {
            Node::rotate_right(node)?;
        }

        // cond3: l_red && r_red
        if let (Some(l), Some(r)) = (&mut node.left, &mut node.right) {
            if l.color == Color::Red && r.color == Color::Red {
                l.color = Color::Black;
                r.color = Color::Black;
                node.color = Color::Red;
            }
        }
        // update node's size
        node.n = node.n();
        Some(node)
    }
}

// deletion
impl<T: Clone + Debug> Node<T> {
    /// if node.left and node.right are both red, mark them black turn node to red.
    fn flip_colors(node: &mut MaybeNode<T>) {
        if let Some(ref mut n) = node {
            Node::flip_colors_inner(n)
        };
    }
    /// if node.left and node.right are both red, mark them black turn node to red.
    fn flip_colors_inner(n: &mut BoxedNode<T>) {
        if let Some(ref mut l) = n.left {
            l.color = l.color.flip();
        }
        if let Some(ref mut r) = n.right {
            r.color = r.color.flip();
        }
        n.color = n.color.flip();
    }

    /// rotate left if node.right is red
    fn balance(node: &mut BoxedNode<T>) -> Option<()> {
        if Node::red(&node.right) {
            Node::rotate_left(node)?;
        }
        Some(())
    }

    fn move_red_left(node: &mut BoxedNode<T>) -> Option<()> {
        Node::flip_colors_inner(node);
        let nr = node.right.as_mut()?;
        if Node::red(&nr.left) {
            Node::rotate_right(nr)?;
            Node::rotate_left(node)?;
            Node::flip_colors_inner(node);
        }
        Some(())
    }

    fn move_red_right(node: &mut BoxedNode<T>) -> Option<()> {
        Node::flip_colors_inner(node);
        // h.left.left == Red
        let cond = match node.left {
            Some(ref l) => Node::red(&l.left),
            None => false,
        };
        if cond {
            Node::rotate_right(node)?;
            Node::flip_colors_inner(node);
        }
        Some(())
    }

    fn delete_min(node: &mut MaybeNode<T>) -> MaybeNode<T> {
        let n = node.as_mut()?;
        match n.left {
            Some(ref mut l) => {
                if l.color == Color::Black && !Node::red(&l.left) {
                    Node::move_red_left(n)?;
                }
            }
            None => {
                return node.take();
            }
        }
        let result = Node::delete_min(&mut n.left);
        Node::balance(n)?;
        result
    }

    fn delete_max(node: &mut MaybeNode<T>) -> MaybeNode<T> {
        let n = node.as_mut()?;
        if Node::red(&n.left) {
            Node::rotate_right(n);
        }
        let n = node.as_mut()?;
        match n.right {
            Some(ref mut r) => {
                if r.color == Color::Black && !Node::red(&r.left) {
                    Node::move_red_right(n)?;
                }
            }
            None => {
                return node.take();
            }
        }
        let result = Node::delete_max(&mut n.right);
        Node::balance(n)?;
        result
    }

    fn delete(node: &mut MaybeNode<T>, key: TextRange) -> MaybeNode<T> {
        let n = node.as_mut()?;
        let result = if key < n.key {
            // n.left != red && n.left.left != red
            if let Some(ref mut l) = n.left {
                if l.color == Color::Black && !Node::red(&l.left) {
                    Node::move_red_left(n).unwrap();
                }
            }
            Node::delete(&mut n.left, key)
        } else {
            if Node::red(&n.left) {
                Node::rotate_right(n).unwrap();
            }
            if key == n.key && n.right.is_none() {
                return node.take();
                // return None;
            }

            let cond = if let Some(ref r) = n.right {
                r.color == Color::Black && !Node::red(&r.left)
            } else {
                true
            };

            if cond {
                Node::move_red_right(n).unwrap();
            }

            // if let Some(ref mut r) = n.right {
            //     if r.color == Color::Black && !Node::red(&r.left) {
            //         Node::move_red_right(n).unwrap();
            //     }
            // }

            if key == n.key {
                let mut result = Node::delete_min(&mut n.right);
                let r_min = result.as_mut().unwrap();
                std::mem::swap(&mut n.val, &mut r_min.val);
                std::mem::swap(&mut n.key, &mut r_min.key);
                result
            } else {
                Node::delete(&mut n.right, key)
            }
        };

        Node::balance(n)?;
        result
    }
}

// intersection
impl<T: Clone + Debug> Node<T> {
    pub fn next(&self) -> Option<&Node<T>> {
        let mut n = self;
        if let Some(ref r) = self.right {
            n = r;
            while let Some(ref l) = n.left {
                n = l;
            }
            return Some(n);
        }
        while let Some(parent) = n.parent_mut() {
            if !n.is_right_child {
                return Some(parent);
            }
            n = parent;
        }
        None
    }

    pub fn next_mut(&mut self) -> Option<&mut Node<T>> {
        let mut n: *mut Node<T> = self;
        if let Some(r) = self.right.as_mut() {
            n = r.as_mut();
            while let Some(ref mut l) = safe_mut(n).left {
                n = l.as_mut();
            }
            return Some(safe_mut(n));
        }
        while let Some(parent) = (safe_mut(n)).parent_mut() {
            if !(safe_mut(n)).is_right_child {
                return Some(parent);
            }
            n = parent;
        }
        None
    }

    pub fn next_raw_box(node: *mut Node<T>) -> Option<*mut Node<T>> {
        let mut n = node;
        if let Some(r) = safe_mut(node).right.as_mut() {
            n = r.as_mut();
            while let Some(ref mut l) = safe_mut(n).left {
                n = l.as_mut();
            }
            return Some(n);
        }
        while let Some(parent) = (safe_mut(n)).parent_mut() {
            if !(safe_mut(n)).is_right_child {
                return Some(parent);
            }
            n = parent;
        }

        None
    }
    pub fn next_raw(&mut self) -> Option<*mut Node<T>> {
        let mut n: *mut Node<T> = self;
        if let Some(r) = self.right.as_mut() {
            n = r.as_mut();
            while let Some(ref mut l) = safe_mut(n).left {
                n = l.as_mut();
            }
            return Some(n);
        }
        while let Some(parent) = (safe_mut(n)).parent_mut() {
            if !(safe_mut(n)).is_right_child {
                return Some(parent);
            }
            n = parent;
        }

        None
    }

    pub fn find_intersects<'a, 'b>(&'a self, range: TextRange, results: &'b mut Vec<&'a Node<T>>) {
        let ord = range.strict_order(&self.key);
        match ord {
            Some(Ordering::Less) => {
                if let Some(ref l) = self.left {
                    l.find_intersects(range, results);
                }
            }
            Some(Ordering::Greater) => {
                if let Some(ref r) = self.right {
                    r.find_intersects(range, results);
                }
            }
            _ => {
                if let Some(ref l) = self.left {
                    l.find_intersects(range, results);
                }
                results.push(self);
                if let Some(ref r) = self.right {
                    r.find_intersects(range, results);
                }
            }
        }
    }

    /// Recursively applies a function to each node in the tree in order.
    /// f is mutable and has type FnMut because it may modify its parameters
    fn apply<F>(&self, f: &mut F)
    where
        F: FnMut(& Node<T>),
    {
        if let Some(ref  l) = self.left {
            l.apply(f);
        }
        f(self);
        if let Some(ref  r) = self.right {
            r.apply(f);
        }
    }

    /// Recursively applies a function to each node in the tree in order.
    /// The function may modify `Node`.
    fn apply_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Node<T>),
    {
        if let Some(ref mut l) = self.left {
            l.apply_mut(f);
        }
        f(self);
        if let Some(ref mut r) = self.right {
            r.apply_mut(f);
        }
    }

    pub fn advance(&mut self, position: usize, length: usize) {
        let cmp = self.key.start > position;
        if cmp {
            if let Some(ref mut l) = self.left {
                l.advance(position, length);
            }
            self.key.advance(length);
            if let Some(ref mut r) = self.right {
                r.apply_mut(&mut |n| n.key.advance(length));
            }
        } else {
            if self.key.end > position {
                // position is inside this interval
                self.key.end += length;
            }
            if let Some(ref mut l) = self.left {
                l.advance(position, length);
            }
            if let Some(ref mut r) = self.right {
                r.advance(position, length)
            }
        }
    }
}

#[derive(Debug, Default)]
/// A interval tree using red-black tree, whereas keys are intervals, and values are
/// plists in elisp.
///
/// All intervals are half-opened intervals, i.e. `I = [start, end)`.These intervals
/// are sorted by their starting point, then their ending point.
///
/// NOTE When inserting an interval I, if I intersects with some existing interval
/// J but I != J, then we split & merge I and J into sub-intervals. Thus all intervals
/// inside a interval tree will not overlap. Adjacant intervals with identical props
/// should be merged afterwards, maybe during redisplay.
pub struct IntervalTree<T: Clone + Debug> {
    pub root: MaybeNode<T>,
}

impl<T: Clone + Debug> IntervalTree<T> {
    /// Creates an empty interval tree.
    pub fn new() -> Self {
        Self { root: None }
    }

    /// Inserts a new interval with the specified `key` and `val` into the interval tree.
    /// 
    /// If the interval `key` is degenerate (i.e., its start equals its end), the function
    /// returns `None` as such intervals are not allowed in the tree. Otherwise, it delegates
    /// the insertion to the underlying node structure.
    /// 
    /// # Arguments
    /// 
    /// * `key` - The text range representing the interval to insert.
    /// * `val` - The value associated with the interval.
    /// * `merge` - A closure that specifies how to merge intervals if they overlap, returning
    ///   a tuple with the merged value and a boolean indicating if the value was changed.
    /// 
    /// # Returns
    /// 
    /// An optional mutable reference to the newly inserted node, or `None` if the interval is
    /// degenerate.
    pub fn insert<'a, F: Fn(T, T) -> anyhow::Result<(T, bool)>>(
        &'a mut self,
        key: impl Into<TextRange>,
        val: T,
        merge: F,
    ) -> Option<&'a mut Box<Node<T>>> {
        let key = key.into();
        if key.start == key.end {
            return None;
        }
        let mut result = Node::insert_at(
            &mut self.root,
            key,
            val,
            std::ptr::null_mut(),
            false,
            &merge,
        );
        result.as_mut().unwrap().color = Color::Black;
        result
    }

    /// Finds the node with key `key` in the tree and returns its value if found.
    /// 
    /// # Arguments
    /// 
    /// * `key` - The text range representing the interval to search for.
    /// 
    /// # Returns
    /// 
    /// An optional value associated with the node if it exists, `None` otherwise.
    pub fn get(&self, key: impl Into<TextRange>) -> Option<T> {
        match self.root {
            Some(ref r) => r.get(key.into()),
            None => None,
        }
    }

    /// Delete the node with key `key` from the tree.
    ///
    /// If the root node is the only black node, then we have to make it red
    /// before deleting. Otherwise, the tree would become unbalanced.
    ///
    /// After deleting, we make sure the root node is black again.
    pub fn delete(&mut self, key: impl Into<TextRange>) -> MaybeNode<T> {
        let key = key.into();
        let result = match self.root {
            Some(ref mut root) => {
                if !Node::red(&root.left) && !Node::red(&root.right) {
                    root.color = Color::Red;
                }

                Node::delete(&mut self.root, key)
            }
            None => None,
        };
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
        result
    }

    /// Deletes the node with the minimum key from the interval tree.
    ///
    /// If the root node is the only black node, it is temporarily colored red
    /// to maintain tree balance during deletion. After deletion, the root node
    /// is recolored black to ensure the red-black tree properties are preserved.
    ///
    /// # Returns
    ///
    /// An optional `Node<T>` representing the removed node, or `None` if
    /// the tree is empty.
    pub fn delete_min(&mut self) -> MaybeNode<T> {
        let root = self.root.as_mut()?;
        if !Node::red(&root.left) && !Node::red(&root.right) {
            root.color = Color::Red;
        }
        let result = Node::delete_min(&mut self.root);
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
        result
    }

    /// Deletes the node with the maximum key from the interval tree.
    ///
    /// If the root node is the only black node, it is temporarily colored red
    /// to maintain tree balance during deletion. After deletion, the root node
    /// is recolored black to ensure the red-black tree properties are preserved.
    ///
    /// # Returns
    ///
    /// An optional `Node<T>` representing the removed node, or `None` if
    /// the tree is empty.
    pub fn delete_max(&mut self) -> MaybeNode<T> {
        let root = self.root.as_mut()?;
        if !Node::red(&root.left) && !Node::red(&root.right) {
            root.color = Color::Red;
        }
        let result = Node::delete_max(&mut self.root);
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
        result
    }

    /// Advances all intervals in the tree by `length`, starting at
    /// `position`. This is typically used to implement operations that insert
    /// or delete text in a buffer.
    pub fn advance(&mut self, position: usize, length: usize) {
        if let Some(ref mut node) = self.root {
            node.advance(position, length);
        }
    }

    /// Find the node whose interval contains the given `position`. If no interval
    /// contains the position, returns `None`.
    pub fn find(&self, position: usize) -> Option<&Node<T>> {
        let range = TextRange::new(position, position + 1);
        let res = self.find_intersects(range);
        res.first().copied()
    }

    /// Find all nodes in the tree whose intervals intersect the given
    /// `range`. The result is a vector of references to the found nodes.
    pub fn find_intersects(&self, range: TextRange) -> Vec<&Node<T>> {
        let mut result = Vec::new();
        if let Some(ref r) = self.root {
            r.find_intersects(range, &mut result);
            // r.satisfy(&|n| n.key.intersects(range), &mut result);
        }
        result
    }

    /// Return the minimum node in the tree, or `None` if the tree is empty.
    pub fn min(&self) -> Option<&Node<T>> {
        self.root.as_ref().map(|n| n.min())
    }

    fn min_mut(&mut self) -> Option<*mut Node<T>> {
        self.root.as_mut().map(|n| n.min_mut() as *mut Node<T>)
            
    }

    /// Merges adjacent intervals in the tree that have equal properties.
    /// 
    /// This function iterates over the nodes in the interval tree, starting from 
    /// the minimum node. It checks if the current node's end equals the next node's 
    /// start and if their values are considered equal by the provided `equal` 
    /// function. If both conditions are met, it merges the intervals by extending 
    /// the current node's end to the next node's end and deletes the next node.
    /// 
    /// # Arguments
    /// 
    /// * `equal` - A closure that takes references to two values and returns `true` 
    ///   if they are considered equal, `false` otherwise.
    pub fn merge<F: Fn(&T, &T) -> bool>(&mut self, equal: F) {
        if let Some(node_ptr) = self.min_mut() {
            let mut node = safe_mut(node_ptr);
            while let Some(next_ptr) = node.next_raw() {
                let next = safe_mut(next_ptr);
                if node.key.end == next.key.start && equal(&node.val, &next.val) {
                    let del = self.delete(next.key).unwrap();
                    node.key.end = del.key.end;
                } else {
                    node = next;
                }
            }
        }
    }

    /// Applies a function to all values in the interval tree. The function is 
    /// given a reference to each value in the tree in order of increasing key 
    /// start. The function is not given any information about the keys.
    pub fn apply<F: FnMut(&T)>(&self, f: &mut F) {
        if let Some(r) = self.root.as_ref() {
            r.apply(&mut |n: &Node<T>| f(&n.val));
        }
    }

    /// Applies a function to all values in the interval tree, modifying the values
    /// in place. The function is given a mutable reference to each value in the
    /// tree in order of increasing key start. The function is not given any
    /// information about the keys.
    pub fn apply_mut<F: FnMut(&mut Node<T>)>(&mut self, f: &mut F) {
        if let Some(r) = self.root.as_mut() {
            r.apply_mut(&mut |n| f(n));
        }
    }

    /// Recursively print out the tree, for debugging purposes. The output format
    /// is not guaranteed to be stable.
    pub fn print(&self) {
        let Some(ref root) = self.root else { return };
        IntervalTree::print_inner(root);
    }

    fn print_inner(node: &Node<T>) {
        println!(
            "key: {:?}, val: {:?}, color: {:?}",
            node.key, node.val, node.color
        );
        if let Some(parent) = unsafe { node.parent.as_ref() } {
            let direction = if node.is_right_child { "right" } else { "left" };
            println!("parent({} child): {:?}", direction, parent.key);
        } else {
            println!("parent: not found");
        }
        if let Some(ref l) = node.left {
            println!("left: ");
            IntervalTree::print_inner(l);
            println!("left end for {:?}", node.key);
        }
        if let Some(ref r) = node.right {
            println!("right: ");
            IntervalTree::print_inner(r);
            println!("right end for {:?}", node.key);
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    fn merge<T: Clone + Debug>(a: T, _b: T) -> anyhow::Result<(T, bool)> {
        Ok((a, false))
    }

    fn build_tree<T: Clone + Debug>(val: T) -> IntervalTree<T> {
        let mut tree = IntervalTree::new();
        tree.insert(TextRange::new(0, 1), val.clone(), merge);
        tree.insert(TextRange::new(1, 2), val.clone(), merge);
        tree.insert(TextRange::new(2, 3), val.clone(), merge);
        tree.insert(TextRange::new(3, 4), val.clone(), merge);
        tree.insert(TextRange::new(4, 5), val.clone(), merge);
        tree.insert(TextRange::new(5, 6), val.clone(), merge);
        tree.insert(TextRange::new(6, 7), val.clone(), merge);
        tree.insert(TextRange::new(7, 8), val.clone(), merge);
        tree.insert(TextRange::new(8, 9), val.clone(), merge);
        tree.insert(TextRange::new(9, 10), val.clone(), merge);
        tree
    }

    #[test]
    fn rotate_left() {
        let val = 1;
        let mut node1 = Node::new_boxed(TextRange::new(0, 3), val);
        node1.color = Color::Black;
        let mut node2 = Node::new_boxed(TextRange::new(3, 6), val);
        let mut node3 = Node::new_boxed(TextRange::new(6, 9), val);
        node3.color = Color::Black;
        let mut node4 = Node::new_boxed(TextRange::new(9, 12), val);
        node4.color = Color::Black;
        let mut node5 = Node::new_boxed(TextRange::new(12, 15), val);
        node5.color = Color::Black;

        node2.left = Some(node3);
        node2.right = Some(node4);
        node2.color = Color::Red;
        node1.right = Some(node2);
        node1.left = Some(node5);
        // let mut node1 = dbg!(node1);
        Node::rotate_left(&mut node1);
        assert_eq!(node1.key.start, 3);
        let n2 = node1.left.unwrap();
        assert_eq!(n2.key.start, 0);
        let n3 = n2.right.unwrap();
        assert_eq!(n3.key.start, 6);
        let n4 = node1.right.unwrap();
        assert_eq!(n4.key.start, 9);
        let n5 = n2.left.unwrap();
        assert_eq!(n5.key.start, 12);

        assert_eq!(node1.color, Color::Black);
        assert_eq!(n2.color, Color::Red);
        assert_eq!(n2.n, 3);
    }

    #[test]
    fn insert() {
        let val = 1;
        let tree = build_tree(val);
        let root = tree.root.as_ref().unwrap();
        assert_eq!(root.key.start, 3);
        let n1 = root.left.as_ref().unwrap();
        assert_eq!(n1.key.start, 1);
        let n2 = root.right.as_ref().unwrap();
        assert_eq!(n2.key.start, 7);
        let n3 = n2.right.as_ref().unwrap();
        assert_eq!(n3.key.start, 9);
        let n4 = n3.left.as_ref().unwrap();
        assert_eq!(n4.key.start, 8);
        assert!(n3.right.is_none())
    }

    #[test]
    fn delete() {
        let val = 1;
        let mut tree = build_tree(val);
        // let mut tree = dbg!(tree);
        for k in vec![8, 4, 5, 7, 3, 6].into_iter() {
            let i = TextRange::new(k, k + 1);
            let a = tree.delete(i).unwrap();
            assert_eq!(a.key, i);
        }
    }

    #[test]
    fn delete_min() {
        let val = 1;
        let mut tree = build_tree(val);
        // let mut tree = dbg!(tree);
        let a = tree.delete_min().unwrap();
        assert_eq!(a.key.start, 0);
    }

    #[test]
    fn find_intersect() {
        let val = 1;
        let tree = build_tree(val);
        let re = tree.find_intersects(TextRange::new(2, 4));
        let k1 = re[0].key;
        let k2 = re[1].key;
        assert_eq!(k1, TextRange::new(2, 3));
        assert_eq!(k2, TextRange::new(3, 4));
        assert_eq!(re.len(), 2);
    }

    #[test]
    fn advance() {
        let val = 1;
        let mut tree = build_tree(val);
        tree.advance(7, 5);
        // let mut tree = dbg!(tree);
        tree.get(TextRange::new(6, 7)).unwrap();
        tree.get(TextRange::new(7, 13)).unwrap();
        tree.get(TextRange::new(13, 14)).unwrap();
        tree.get(TextRange::new(14, 15)).unwrap();
    }

    #[test]
    fn find_next() {
        let val = 1;
        let mut tree = build_tree(val);
        // tree.print();
        tree.delete(TextRange::new(5, 6));
        let mut n = tree.min().unwrap();

        loop {
            match n.next() {
                Some(ne) => {
                    n = ne;
                    // println!("{:?}", ne.key);
                }
                None => break,
            }
        }
        assert_eq!(n.key.start, 9)
    }

    #[test]
    fn test_merge_adjacent_intervals_with_equal_properties() {
        let mut tree = IntervalTree::new();
        tree.insert(TextRange::new(1, 5), 1, merge);
        tree.insert(TextRange::new(5, 10), 1, merge);
        tree.merge(|a, b| *a == *b);
        assert_eq!(tree.find_intersects(TextRange::new(1, 10)).len(), 1);
    }

    #[test]
    fn test_not_merge_adjacent_intervals_with_different_properties() {
        let mut tree = IntervalTree::new();
        tree.insert(TextRange::new(1, 5), 1, merge);
        tree.insert(TextRange::new(5, 10), 2, merge);
        tree.merge(|a, b| *a == *b);
        assert_eq!(tree.find_intersects(TextRange::new(1, 10)).len(), 2);
    }

    #[test]
    fn test_not_merge_non_adjacent_intervals() {
        let mut tree = IntervalTree::new();
        tree.insert(TextRange::new(1, 5), 1, merge);
        tree.insert(TextRange::new(10, 15), 1, merge);
        tree.merge(|a, b| *a == *b);
        assert_eq!(tree.find_intersects(TextRange::new(1, 15)).len(), 2);
    }

    #[test]
    fn test_merge_multiple_adjacent_intervals_with_equal_properties() {
        let mut tree = IntervalTree::new();
        tree.insert(TextRange::new(5, 10), 1, merge);
        tree.insert(TextRange::new(1, 5), 1, merge);
        tree.insert(TextRange::new(10, 15), 1, merge);
        tree.merge(|a, b| *a == *b);
        assert_eq!(tree.find_intersects(TextRange::new(1, 15)).len(), 1);
    }

    #[test]
    fn test_handle_empty_tree() {
        let mut tree: IntervalTree<i32> = IntervalTree::new();
        tree.merge(|a, b| *a == *b);
        assert_eq!(tree.find_intersects(TextRange::new(1, 10)).len(), 0);
    }

    #[test]
    fn test_handle_tree_with_single_node() {
        let mut tree = IntervalTree::new();
        tree.insert(TextRange::new(1, 5), 1, merge);
        tree.merge(|a, b| *a == *b);
        assert_eq!(tree.find_intersects(TextRange::new(1, 5)).len(), 1);
    }
}
