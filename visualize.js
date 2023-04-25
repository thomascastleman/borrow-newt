const stage = new Stage();

const program = instance.signature('Program').atoms()[0];
const program_start_field = instance.field('program_start');
const next_field = instance.field('next');
const inner_scope_field = instance.field('inner_scope');

// First statement of the entire program
const first_statement = program.join(program_start_field);

// Check if a sig has a given field defined.
function hasField(sig, field) {
    return sig.join(field).tuples().length != 0;
}

// Convert a sequence of statements into Rust syntax
function convertToProgramText(starting_statement) {
    let text = "";
    curr_statement = starting_statement;

    while (true){
        // TODO: Convert this statement to string, add to text
        text += "STATEMENT\n";

        // If there is an inner scope, convert that whole thing to text, add to text
        if (hasField(curr_statement, inner_scope_field)) {
            text += "{\n";
            text += convertToProgramText(curr_statement.join(inner_scope_field)) + "\n";
            text += "}\n";
        }

        // Move to the next statement
        if (hasField(curr_statement, next_field)) {
            curr_statement = curr_statement.join(next_field);
        } else {
            break;
        }
    }

    return text;
}

// FIXME: For now, just log to console. We need to find out 
// how to display unformatted text (that includes our newlines)
// in the visualizer.
console.log(convertToProgramText(first_statement));

stage.add(new TextBox(`${convertToProgramText(first_statement)}`, {x:300, y:100},'black',16));
stage.render(svg, document);
