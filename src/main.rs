mod ast;
mod cmd;
mod lexer;
mod opt;
mod parser;
mod repl;

use parser::Parser;

fn main() {
    let mut parser = Parser::new();
    if !opt::parse_cmdline_options(&mut parser) {
        return;
    }
    repl::read_eval_print_loop(parser);
}
