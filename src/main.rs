use interval_tree::{IntervalTree, TextRange};

fn merge<T>(a: T, _b: T) -> anyhow::Result<(T, bool)> {
    Ok((a, false))
}

fn main() {
    let mut tree = IntervalTree::new();
    tree.insert(TextRange::new(5, 10), 1, merge);
    tree.insert(TextRange::new(1, 5), 1, merge);
    // tree.insert(TextRange::new(10, 15), 1, merge);
    tree.print();
    println!("\n\n---\n\n");
    // tree.delete(TextRange::new(5, 10));
    tree.delete(TextRange::new(10, 15));
    tree.print();
}
