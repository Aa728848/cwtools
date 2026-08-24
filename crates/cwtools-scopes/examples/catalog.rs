use cwtools_scopes::game::{GameScopeFamily, catalog};
fn main() {
    let games = [
        ("ck2", GameScopeFamily::Ck2),
        ("ck3", GameScopeFamily::Ck3),
        ("eu4", GameScopeFamily::Eu4),
        ("eu5", GameScopeFamily::Eu5),
        ("hoi4", GameScopeFamily::Hoi4),
        ("ir", GameScopeFamily::Imperator),
        ("vic2", GameScopeFamily::Vic2),
        ("vic3", GameScopeFamily::Vic3),
        ("stellaris", GameScopeFamily::Stellaris),
    ];
    print!("[");
    for (i, (name, game)) in games.into_iter().enumerate() {
        if i > 0 {
            print!(",");
        }
        let c = catalog(game);
        print!("{{\"name\":\"{name}\",\"transitions\":[");
        for (j, (key, _)) in c.transitions.iter().enumerate() {
            if j > 0 {
                print!(",");
            }
            print!("\"{key}\"");
        }
        print!("],\"effectCount\":{}}}", c.effects.len());
    }
    print!("]");
}
