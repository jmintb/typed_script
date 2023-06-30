use pest::Parser;
use pest_derive::{self, Parser};

#[derive(Parser)]
#[grammar = "typed_script.pest"]
struct TSParser;

pub enum TSExpression {
    Value(TSValue)
}

pub enum TSValue {
   String,
   Number,
   Boolean,
}

pub enum TSType {
    String,
    Number,
    Boolean
}

pub struct TSIdentifier(String);

pub enum TSAST {
    Value(TSValue),
    Expression(TSExpression),
    Assignment(TSIdentifier, TSExpression) 
}

pub enum TypedAst {
    Value(TSValue, TSType),
    Expression(TSExpression, TSType),
    Assignment(TSIdentifier, TSExpression, TSType) 
}


fn main() {
    let parsed_res = TSParser::parse(Rule::program, "let myvar = \"test\";").unwrap();
    
    let mut ast: Vec<TSAST> = vec![];

    for rule in parsed_res{
       match rule.as_rule(){
            Rule::program => println!("{}", rule),
            Rule::expression => println!("{}", rule),
            Rule::assignment => println!("{}", rule),
            _ => println!("{}", rule)
        }
    }

}

fn parse_assignment(assignment: Rule::assignment) -> Result<TAST, Box<dyn std::error::Error>> {

    let mut inner_rules = assignment.into_inner();

    inner_rules.next();

    let identifier = inner_rules.next().unwrap();
    
    inner_rules.next();

    let expression = inner_rules.next().unwrap();

    println!("id: {identifier}, exp: {expression} ");

    todo!()
}
