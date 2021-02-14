use arr_macro::arr;
use std::{cmp::min, fmt, mem};

enum Node<T> {
    None,
    Leaf(Option<T>),
    Path(Box<Path<T>>),
    Container4(Box<Container4<T>>),
    Container256(Box<Container256<T>>),
}

impl<T> Default for Node<T> {
    fn default() -> Self {
        Node::None
    }
}

struct Path<T> {
    key: Vec<u8>,
    child: Node<T>,
}

// wrap_path_in_container returns a new container that contains the path.
fn wrap_path_in_container<T>(n: &mut Node<T>) -> Box<Container4<T>> {
    if let Node::Path(p) = n {
        let mut c = Box::new(Container4::<T> {
            keys: [p.key.remove(0), 0, 0, 0],
            children: [Node::None, Node::None, Node::None, Node::None],
            count: 1,
            value: None,
        });
        // path.key might be empty now, in which case we can put the path child directly
        // into the new container rather than the remaining path
        c.children[0] = if p.key.is_empty() {
            mem::take(&mut p.child)
        } else {
            mem::take(n)
        };
        c
    } else {
        panic!("wrap_path_in_container should be called with a Node::Path");
    }
}

fn split_path_maybe<T>(n: &mut Node<T>, k: &[u8]) -> Option<Node<T>> {
    if let Node::Path(p) = n {
        // if k has a prefix of p, then we're okay, otherwise we need
        // to split this path where the common prefix ends.

        let prefix_len = common_prefix_len(k, p.key.as_slice());
        if prefix_len < p.key.len() {
            // mutate path(child) to path(container(path(child)))
            let head = p.key[..prefix_len].to_vec();
            p.key = p.key[prefix_len..].to_vec();
            let c = wrap_path_in_container(n);
            // its possible that there's no matching prefix at all.
            // In that case we can use the container we just built as the result
            // otherwise we need a path to the container
            return if head.is_empty() {
                Some(Node::Container4(c))
            } else {
                Some(Node::Path(Box::new(Path {
                    key: head,
                    child: Node::Container4(c),
                })))
            };
        }
        None
    } else {
        panic!("split_path_maybe should be called with a Node::Path");
    }
}
struct Container4<T> {
    keys: [u8; 4],
    children: [Node<T>; 4],
    count: usize,
    value: Option<T>,
}

impl<T> Container4<T> {
    fn new() -> Self {
        Container4::<T> {
            keys: [0; 4],
            children: [Node::None, Node::None, Node::None, Node::None],
            count: 0,
            value: None,
        }
    }
    fn new_from_c256(src: &mut Container256<T>) -> Container4<T> {
        let mut n = Self::new();
        std::mem::swap(&mut src.value, &mut n.value);
        for k in 0..256 {
            if matches!(src.children[k], Node::None) {
                continue;
            }
            n.keys[n.count] = k as u8;
            std::mem::swap(&mut n.children[n.count], &mut src.children[k]);
            n.count += 1;
        }
        n
    }
    fn should_grow(&self, key: u8) -> bool {
        if self.count < 4 {
            return false;
        }
        matches!(self.get_child(key), Node::None)
    }
    // returns a smaller node that is logically equivalent to this one
    fn shrink_maybe(&mut self) -> Option<Node<T>> {
        if self.count == 1 && self.value.is_none() {
            let mut c = Node::None;
            mem::swap(&mut c, &mut self.children[0]);
            if let Node::Path(cp) = c {
                // if the child is a path, we can coalesce the 2 together.
                let mut new_key = vec![self.keys[0]];
                new_key.extend_from_slice(&cp.key);
                Some(Node::Path(Box::new(Path {
                    key: new_key,
                    child: cp.child,
                })))
            } else {
                // otherwise we need to wrap it in a path to capture the child's key
                Some(Node::Path(Box::new(Path {
                    key: vec![self.keys[0]],
                    child: c,
                })))
            }
        } else if self.count == 0 && self.value.is_some() {
            let mut v = None;
            mem::swap(&mut v, &mut self.value);
            Some(Node::Leaf(v))
        } else {
            None
        }
    }
    fn remove_child_at_index(&mut self, idx: usize) {
        for i in idx..self.count {
            let mut k = 0u8;
            let mut t = Node::None;
            if i != self.count - 1 {
                mem::swap(&mut self.keys[i + 1], &mut k);
                mem::swap(&mut self.children[i + 1], &mut t);
            }
            mem::swap(&mut self.keys[i], &mut k);
            mem::swap(&mut self.children[i], &mut t);
        }
        self.count -= 1;
    }

    fn get_child(&self, key: u8) -> &Node<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return &self.children[i];
            }
        }
        &Node::None
    }
    fn get_child_slot(&mut self, key: u8, create: bool) -> Option<(&mut Node<T>, usize)> {
        let mut insertion_point = self.count;
        for i in 0..self.count {
            if self.keys[i] == key {
                return Some((&mut self.children[i], i));
            }
            if self.keys[i] > key {
                insertion_point = i;
                break;
            }
        }
        if !create {
            return None;
        }
        assert!(self.count < 4, "container should of been grown already");
        // store key in order.
        for idx in (insertion_point..self.count).rev() {
            let mut k: u8 = 0;
            let mut c = Node::None;
            mem::swap(&mut k, &mut self.keys[idx]);
            mem::swap(&mut k, &mut self.keys[idx + 1]);
            mem::swap(&mut c, &mut self.children[idx]);
            mem::swap(&mut c, &mut self.children[idx + 1]);
        }
        self.keys[insertion_point] = key;
        self.count += 1;
        Some((&mut self.children[insertion_point], insertion_point))
    }
}

struct Container256<T> {
    children: [Node<T>; 256],
    value: Option<T>,
}

impl<T> Container256<T> {
    fn new(src: &mut Box<Container4<T>>) -> Container256<T> {
        let mut n = Container256 {
            children: arr![Node::None; 256],
            value: None,
        };
        std::mem::swap(&mut src.value, &mut n.value);
        for i in 0..src.count {
            let x = &mut src.children[i];
            let y = &mut n.children[src.keys[i] as usize];
            std::mem::swap(x, y);
        }
        n
    }

    // index_of_next returns the index (aka key) of the next populated child
    // after k, or returns None if we've run off the end.
    fn index_of_next(&self, k: usize, include_k: bool) -> Option<usize> {
        assert!(k < 256);
        let start = if include_k { k } else { k + 1 };
        for i in start..256 {
            if !matches!(self.children[i], Node::None) {
                return Some(i);
            }
        }
        None
    }

    // returns a smaller node that is logically equivalent to this one
    fn shrink_maybe(&mut self) -> Option<Node<T>> {
        let is_small = self
            .children
            .iter()
            .filter(|n| !matches!(n, Node::None))
            .nth(3)
            .is_none();
        if is_small {
            Some(Node::Container4(Box::new(Container4::new_from_c256(self))))
        } else {
            None
        }
    }
}

pub struct Tree<T> {
    root: Node<T>,
}

impl<T> Default for Tree<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for Tree<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write_node(f, &self.root, 0)
    }
}

impl<T> Tree<T> {
    pub fn new() -> Self {
        Self { root: Node::None }
    }

    pub fn put(&mut self, key: &[u8], value: T) {
        let mut n = &mut self.root;
        let mut k = key;
        while !k.is_empty() {
            if let Node::Container4(c) = n {
                if c.should_grow(k[0]) {
                    *n = Node::Container256(Box::new(Container256::new(c)));
                }
            }
            if let Node::Path(_) = n {
                if let Some(new_node) = split_path_maybe(n, k) {
                    *n = new_node
                }
            }
            match n {
                Node::None => {
                    // We've reached the bottom of the tree for this branch, we can create
                    // a path + leaf to handle the remaining key
                    *n = Node::Path(Box::new(Path {
                        key: k.to_vec(),
                        child: Node::Leaf(Some(value)),
                    }));
                    return;
                }
                Node::Path(p) => {
                    // at this point p must be a prefix of k. (due to split_path_maybe call above)
                    assert!(k.starts_with(p.key.as_slice()));
                    n = &mut p.child;
                    k = &k[p.key.len()..];
                }
                Node::Leaf(v) => {
                    let mut c = Box::new(Container4::new());
                    mem::swap(v, &mut c.value);
                    *n = Node::Container4(c);
                }
                Node::Container4(c) => {
                    // can't return None unless it wasn't grown when it should of been.
                    let child = c.get_child_slot(k[0], true).unwrap();
                    n = child.0;
                    k = &k[1..]
                }
                Node::Container256(c) => {
                    n = &mut c.children[k[0] as usize];
                    k = &k[1..]
                }
            }
        }
        match n {
            Node::None => {
                *n = Node::Leaf(Some(value));
            }
            Node::Leaf(v) => {
                *v = Some(value);
            }
            Node::Path(_) => {
                let mut c = wrap_path_in_container(n);
                c.value = Some(value);
                *n = Node::Container4(c);
            }
            Node::Container4(c) => {
                c.value = Some(value);
            }
            Node::Container256(c) => {
                c.value = Some(value);
            }
        }
    }

    pub fn delete(&mut self, key: &[u8]) {
        fn delete_one<T>(n: &mut Node<T>, key: &[u8]) -> Option<Node<T>> {
            match n {
                Node::None => None,
                Node::Leaf(_) => {
                    if key.is_empty() {
                        Some(Node::None)
                    } else {
                        None
                    }
                }
                Node::Path(p) => {
                    if !key.starts_with(&p.key) {
                        return None;
                    }
                    match delete_one(&mut p.child, &key[p.key.len()..]) {
                        Some(new_child) => {
                            if matches!(new_child, Node::None) {
                                Some(Node::None)
                            } else {
                                if let Node::Path(child_path) = new_child {
                                    // if the child is a path, we can fold the 2 paths into one.
                                    p.key.extend(child_path.key.iter());
                                    p.child = child_path.child;
                                } else {
                                    p.child = new_child;
                                }
                                None
                            }
                        }
                        None => None,
                    }
                }
                Node::Container4(c) => {
                    if key.is_empty() {
                        c.value = None;
                        return c.shrink_maybe();
                    }
                    let child = c.get_child_slot(key[0], false);
                    match child {
                        Some((next, idx)) => match delete_one(next, &key[1..]) {
                            Some(new_child) => {
                                if matches!(new_child, Node::None) {
                                    c.remove_child_at_index(idx);
                                    return c.shrink_maybe();
                                } else {
                                    c.children[idx] = new_child;
                                }
                                None
                            }
                            None => None,
                        },
                        None => None,
                    }
                }
                Node::Container256(c) => {
                    if key.is_empty() {
                        c.value = None;
                        return c.shrink_maybe();
                    }
                    let i = key[0] as usize;
                    match delete_one(&mut c.children[i], &key[1..]) {
                        Some(new_child) => {
                            let is_none = matches!(new_child, Node::None);
                            c.children[i] = new_child;
                            if is_none {
                                c.shrink_maybe()
                            } else {
                                None
                            }
                        }
                        None => None,
                    }
                }
            }
        }
        if let Some(new_child) = delete_one(&mut self.root, key) {
            self.root = new_child;
        }
    }

    pub fn get(&self, key: &[u8]) -> Option<&T> {
        let mut n = &self.root;
        let mut k = key;
        loop {
            match n {
                Node::Leaf(t) => {
                    if k.is_empty() {
                        return t.as_ref();
                    } else {
                        return None;
                    }
                }
                Node::Path(p) => {
                    if k.len() < p.key.len() {
                        return None;
                    }
                    if p.key.as_slice() != &k[..p.key.len()] {
                        return None;
                    }
                    n = &p.child;
                    k = &k[p.key.len()..]
                }
                Node::Container4(c) => {
                    if k.is_empty() {
                        return c.value.as_ref();
                    }
                    n = c.get_child(k[0]);
                    k = &k[1..];
                }
                Node::Container256(c) => {
                    if k.is_empty() {
                        return c.value.as_ref();
                    }
                    n = &c.children[k[0] as usize];
                    k = &k[1..];
                }
                Node::None => return None,
            };
        }
    }

    pub fn sizes(&self) -> Sizes {
        let mut s = Sizes::default();
        fn w<T>(s: &mut Sizes, n: &Node<T>) {
            match n {
                Node::None => {}
                Node::Leaf(_) => {
                    s.leaf += 1;
                    s.value += 1;
                }
                Node::Path(p) => {
                    s.path += 1;
                    w(s, &p.child);
                }
                Node::Container4(c) => {
                    s.c4 += 1;
                    if c.value.is_some() {
                        s.value += 1;
                    }
                    for i in 0..c.count {
                        w(s, &c.children[i]);
                    }
                }
                Node::Container256(c) => {
                    s.c256 += 1;
                    if c.value.is_some() {
                        s.value += 1;
                    }
                    c.children.iter().for_each(|x| w(s, x));
                }
            }
        };
        w(&mut s, &self.root);
        s
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            pos: vec![IterState {
                n: &self.root,
                key: vec![],
                pos: 0,
                check_value: true,
            }],
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq)]
pub struct Sizes {
    leaf: usize,
    path: usize,
    c4: usize,
    c256: usize,
    value: usize,
}

pub struct Iter<'a, T> {
    pos: Vec<IterState<'a, T>>,
}

struct IterState<'a, T> {
    n: &'a Node<T>,
    key: Vec<u8>,
    pos: usize,
    check_value: bool,
}

impl<'a, T> Iter<'a, T> {
    fn push(&mut self, n: &'a Node<T>, key: Vec<u8>, pos: usize) {
        self.pos.push(IterState {
            n,
            key,
            pos,
            check_value: false,
        });
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Vec<u8>, &'a T);
    // the last item in pos is where we start to find the next
    // value to return
    fn next(&mut self) -> Option<Self::Item> {
        let mut s = self.pos.pop()?;
        loop {
            match s.n {
                Node::None => {
                    return None;
                }
                Node::Leaf(v) => return Some((s.key, v.as_ref().unwrap())),
                Node::Path(p) => {
                    s.n = &p.child;
                    s.key.extend(p.key.iter());
                }
                Node::Container4(c) => {
                    if s.check_value {
                        if c.value.is_some() {
                            self.push(s.n, s.key.clone(), 0);
                            return Some((s.key, c.value.as_ref().unwrap()));
                        }
                        s.pos = 0;
                    }
                    if c.count > s.pos + 1 {
                        self.push(s.n, s.key.clone(), s.pos + 1);
                    }
                    s.n = &c.children[s.pos];
                    s.key.extend_from_slice(&[c.keys[s.pos]]);
                }
                Node::Container256(c) => {
                    if s.check_value {
                        // A container must have at least one child, so the unwrap is safe here
                        s.pos = c.index_of_next(0, true).unwrap();
                        if c.value.is_some() {
                            self.push(s.n, s.key.clone(), s.pos);
                            return Some((s.key, c.value.as_ref().unwrap()));
                        }
                    }
                    if let Some(next) = c.index_of_next(s.pos, false) {
                        self.push(s.n, s.key.clone(), next);
                    }
                    s.n = &c.children[s.pos];
                    s.key.extend_from_slice(&[s.pos as u8]);
                }
            }
            s.check_value = true;
        }
    }
}

fn write_node<T: std::fmt::Debug, W: fmt::Write>(
    f: &mut W,
    n: &Node<T>,
    indent: i32,
) -> fmt::Result {
    match n {
        Node::None => {
            // nothing
        }
        Node::Leaf(t) => match &t {
            Some(v) => writeln!(f, "<leaf> {:?}", v)?,
            None => panic!("Leaf should never have a None value"),
        },
        Node::Path(p) => {
            let path = format!("<path> {:?} : ", p.key);
            f.write_str(&path)?;
            write_node(f, &p.child, indent + 1 + (path.len() as i32))?;
        }
        Node::Container4(c) => {
            write!(f, "<c4> : ")?;
            match &c.value {
                Some(v) => writeln!(f, "<value> {:?}", v)?,
                None => f.write_char('\n')?,
            }
            let new_indent = indent + 2;
            for i in 0..c.count {
                write_indent(f, new_indent)?;
                write!(f, "[{}]: ", c.keys[i])?;
                write_node(f, &c.children[i], new_indent + 4)?;
            }
        }
        Node::Container256(c) => {
            write!(f, "<c256> : ")?;
            match &c.value {
                Some(v) => writeln!(f, "<value> {:?}", v)?,
                None => f.write_char('\n')?,
            }
            let new_indent = indent + 4;
            c.children
                .iter()
                .enumerate()
                .filter(|(_, c)| !matches!(c, Node::None))
                .try_for_each(|(k, child)| -> fmt::Result {
                    write_indent(f, new_indent)?;
                    write!(f, "[{}]: ", k)?;
                    write_node(f, child, new_indent + 4)
                })?;
        }
    }
    Ok(())
}

fn write_indent<W: fmt::Write>(f: &mut W, indent: i32) -> fmt::Result {
    for _ in 0..indent {
        f.write_char(' ')?;
    }
    Ok(())
}

fn common_prefix_len(a: &[u8], b: &[u8]) -> usize {
    let len = min(a.len(), b.len());
    for i in 0..len {
        if a[i] != b[i] {
            return i;
        }
    }
    len
}

#[cfg(test)]
mod test {
    use super::*;
    use insta::assert_debug_snapshot;

    #[test]
    fn container4_only() {
        let mut x = Tree::<String>::new();
        x.put(&[1, 2], String::from("alice"));
        x.put(&[1, 2, 3], String::from("bob"));
        x.put(&[2, 10, 11, 12, 13, 14], String::from("eve"));
        x.put(&[2, 10, 11], String::from("jim"));

        assert_eq!(x.get(&[1, 2]), Some(&String::from("alice")));
        assert_eq!(x.get(&[1, 2, 3]), Some(&String::from("bob")));
        assert_eq!(x.get(&[2, 10, 11, 12, 13, 14]), Some(&String::from("eve")));
        assert_eq!(x.get(&[2, 10, 11]), Some(&String::from("jim")));

        assert_eq!(x.get(&[5]), None);
        assert_eq!(x.get(&[]), None);
        assert_eq!(x.get(&[2, 10]), None);
        assert_eq!(x.get(&[2, 10, 11, 12]), None);
        assert_eq!(x.get(&[2, 10, 11, 12, 13, 14, 15]), None);

        assert_debug_snapshot!(x);
    }

    #[test]
    fn update_existing_key() {
        let mut x = Tree::new();
        x.put(&[2], 2);
        x.put(&[2], 4);
        assert_eq!(x.get(&[2]), Some(&4));
        let mut it = x.iter();
        assert_eq!(it.next(), Some((vec![2], &4)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn container4_grow_to_256() {
        let mut x = Tree::<u8>::new();
        for i in 10..50 {
            x.put(&[1, 2, 3, i], i);
        }
        x.put(&[1, 2, 3], 255);
        for i in 10..50 {
            assert_eq!(x.get(&[1, 2, 3, i]), Some(&i));
        }
        assert_debug_snapshot!(x);
    }

    #[test]
    fn debug_tree() {
        let mut x = Tree::<usize>::new();
        let k: &[u8] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        for i in 1..k.len() {
            x.put(&k[..i], i * 100);
            x.put(&[1, 2, 3, i as u8, 4, 5, 6], i * 100);
        }
        assert_debug_snapshot!(x);
    }

    #[test]
    fn tree_iter() {
        let mut x = Tree::<usize>::new();
        x.put(&[1, 2, 3], 1);
        x.put(&[1, 2, 3, 4], 2);
        x.put(&[2, 3], 3);
        let mut it = x.iter();

        assert_eq!(it.next(), Some((vec![1, 2, 3], &1)));
        assert_eq!(it.next(), Some((vec![1, 2, 3, 4], &2)));
        assert_eq!(it.next(), Some((vec![2, 3], &3)));
        assert_eq!(it.next(), None);
        assert_debug_snapshot!(x);
    }

    #[test]
    fn tree_iter_key_order() {
        let mut x = Tree::new();
        x.put(&[2, 2], 2);
        x.put(&[2, 1], 1);
        x.put(&[2, 3], 3);
        let mut it = x.iter();
        assert_eq!(it.next(), Some((vec![2, 1], &1)));
        assert_eq!(it.next(), Some((vec![2, 2], &2)));
        assert_eq!(it.next(), Some((vec![2, 3], &3)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn tree_iter_256() {
        let mut x = Tree::<usize>::new();
        for i in 0..10 {
            x.put(&[1, 2, i + 10], i as usize);
        }
        x.put(&[1, 2, 255], 10);
        assert_debug_snapshot!(x);
        let mut it = x.iter();
        for i in 0..10 {
            assert_eq!(it.next(), Some((vec![1, 2, i + 10], &(i as usize))));
        }
        assert_eq!(it.next(), Some((vec![1, 2, 255], &10)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn tree_iter_depth() {
        let mut x = Tree::<usize>::new();
        let k = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        k.iter()
            .enumerate()
            .for_each(|(i, _)| x.put(&k[0..i], i + 10));

        assert_debug_snapshot!(x);
        let mut it = x.iter();
        k.iter()
            .enumerate()
            .for_each(|(i, _)| assert_eq!(it.next(), Some((k[0..i].to_vec(), &(i + 10)))));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn delete() {
        let mut x = Tree::new();
        x.delete(&[1]);
        x.put(&[1, 2, 3], 1);
        x.put(&[1, 2, 4], 2);
        x.put(&[1, 2, 5], 3);
        x.delete(&[1]);
        x.delete(&[1, 2, 3]);
        assert_debug_snapshot!(x);
        let mut it = x.iter();
        assert_eq!(it.next(), Some((vec![1, 2, 4], &2)));
        assert_eq!(it.next(), Some((vec![1, 2, 5], &3)));
        assert_eq!(it.next(), None);

        x.delete(&[1, 2, 4]);
        x.delete(&[1, 2, 5]);
        if !matches!(x.root, Node::None) {
            panic!("root should be None but isn't");
        }
    }

    #[test]
    fn delete_256() {
        let mut x = Tree::new();
        x.delete(&[1]);
        for i in 10..20 {
            x.put(&[i, 2, 3], 1);
            x.put(&[i, 2, 4], 2);
            x.put(&[i, i, 5], 3);
        }
        x.delete(&[15, 2, 3]);
        assert_eq!(
            Sizes {
                path: 11,
                leaf: 29,
                value: 29,
                c256: 1,
                c4: 19,
            },
            x.sizes()
        );
        assert_debug_snapshot!(x);
        assert_eq!(x.iter().count(), 29);
        for i in 10..20 {
            x.delete(&[i, 2, 3]);
            x.delete(&[i, 2, 4]);
            x.delete(&[i, i, 5]);
        }
        if !matches!(x.root, Node::None) {
            panic!("root should be None but isn't");
        }
    }

    #[test]
    fn test_path_coalesce() {
        let mut x = Tree::<usize>::new();
        x.put(&[1, 2, 3], 1);
        x.put(&[1, 2, 3, 4, 5, 6], 2);
        assert_debug_snapshot!(x, @r###"
        <path> [1, 2, 3] : <c4> : <value> 1
                              [4]: <path> [5, 6] : <leaf> 2
        "###);
        x.delete(&[1, 2, 3]);
        assert_debug_snapshot!(x, @"<path> [1, 2, 3, 4, 5, 6] : <leaf> 2
");
    }

    #[test]
    fn test_c256_to_c4() {
        let mut x = Tree::new();
        x.put(&[], 42);
        for i in 10..20 {
            x.put(&[i], 100 + i);
            assert_eq!(x.get(&[i]), Some(&(100 + i)));
        }
        for i in 10..18 {
            x.delete(&[i])
        }
        assert_debug_snapshot!(x, @r###"
        <c4> : <value> 42
          [18]: <leaf> 118
          [19]: <leaf> 119
        "###);
        x.delete(&[18]);
        assert_debug_snapshot!(x, @r###"
        <c4> : <value> 42
          [19]: <leaf> 119
        "###);
        x.delete(&[19]);
        assert_debug_snapshot!(x, @"<leaf> 42
");
    }
}
