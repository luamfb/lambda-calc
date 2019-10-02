mod repl;
mod lexer;
mod parser;
mod ast;

fn main() {
    repl::read_eval_print_loop();
}
