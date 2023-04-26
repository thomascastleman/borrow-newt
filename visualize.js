const stage = new Stage();

const program = instance.signature('Program').atoms()[0];
const program_start_field = instance.field('program_start');
const next_field = instance.field('next');
const inner_scope_field = instance.field('inner_scope');
const declared_variable_field = instance.field('declared_variable');
const initialized_variable_field = instance.field('initialized_variable');
const initial_value_field = instance.field('initial_value');
const updated_variable_field = instance.field("updated_variable");
const new_value_field = instance.field('new_value');
const moved_value_field = instance.field("moved_value");
const source_field = instance.field("source");
const destination_field = instance.field("destination");
const borrow_field = instance.field("borrow_referent");
const borrow_mut_field = instance.field("borrow_mut_referent");

// First statement of the entire program
const first_statement = program.join(program_start_field);
let x_offset = 300; // 40;
let y_offset = 20;

// Check if a sig has a given field defined.
function hasField(sig, field) {
    return sig.join(field).tuples().length != 0;
}

// Convert a sequence of statements into Rust syntax
function convertToProgramText(starting_statement) {
    curr_statement = starting_statement;

    while (true){
        // TODO: Convert this statement to string, add to text

        //statement is a declaration
        if (hasField(curr_statement, declared_variable_field)) {
            const variable = curr_statement.join(declared_variable_field);
            text = 'let ' + variable + ';'
            stage.add(new TextBox(`${text}`, {x:x_offset, y:y_offset},'black'));
        }

        //statement is an initialization
        else if (hasField(curr_statement, initialized_variable_field)) {
            const variable = curr_statement.join(initialized_variable_field);
            const value = curr_statement.join(initial_value_field);
            text = ''+ variable + ' = ' 
            text += value + ';'
            if (hasField(value, borrow_field)) {
                text += ' (borrow)'
            }
            else if (hasField(value, borrow_mut_field)) {
                text += ' (borrow mut)'
            }
            stage.add(new TextBox(`${text}`, {x:x_offset, y:y_offset},'black',16));
        }

        //statement is an update
        else if (hasField(curr_statement, updated_variable_field)) {
            const variable = curr_statement.join(updated_variable_field);
            const value = curr_statement.join(new_value_field);
            text = variable + ' = '
            if (hasField(value, borrow_field)) {
                text += '&' + value.join(borrow_field) + ';';
            }
            else if (hasField(value, borrow_mut_field)) {
                text += '&mut ' + value.join(borrow_mut_field); + ';';
            } else {
                text += value + ';'
            }

            stage.add(new TextBox(`${text}`, {x:x_offset, y:y_offset},'black',16));
        }

        else if (hasField(curr_statement, moved_value_field)) {
            const src = curr_statement.join(source_field);
            const dst = curr_statement.join(destination_field);
            text = src + ' = '
            text += dst + ';'
            stage.add(new TextBox(`${text}`, {x:x_offset, y:y_offset},'black',16));
        }

        else if (!hasField(curr_statement, inner_scope_field)) {
            stage.add(new TextBox(`{}`, {x:x_offset, y:y_offset},'black',16));
        }
        y_offset += 20;

        // If there is an inner scope, convert that whole thing to text, add to text
        if (hasField(curr_statement, inner_scope_field)) {
            stage.add(new TextBox(`{`, {x:x_offset, y:y_offset},'black',16));
            y_offset += 20;
            x_offset += 20;
            convertToProgramText(curr_statement.join(inner_scope_field));
            x_offset -= 20
            stage.add(new TextBox(`}`, {x:x_offset, y:y_offset},'black',16));
            y_offset += 20;
        }

        // Move to the next statement
        if (hasField(curr_statement, next_field)) {
            curr_statement = curr_statement.join(next_field);
        } else {
            break;
        }
    }
}

// FIXME: For now, just log to console. We need to find out 
// how to display unformatted text (that includes our newlines)
// in the visualizer.
console.log(convertToProgramText(first_statement));

// stage.add(new TextBox(`${convertToProgramText(first_statement)}`, {x:300, y:100},'black',16));
// stage.add(new TextBox(`Hello`, {x:300, y:100},'black',16));
stage.render(svg, document);
