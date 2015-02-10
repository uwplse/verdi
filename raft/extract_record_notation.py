# This is the hackiest thing, but it will come in handy.

import sys
import re

file_name = sys.argv[1]
record_name = sys.argv[2]

file = open(file_name).read()

comment_regex = r'\(\*.*\*\)'
record_regex = r'(Record %s.*\{(.*)\}\.)' % record_name
record_sep = ';'
field_name_regex = r'\s*(\w+)\s*:\s*'
variable_regex = r'Variable ([^.]*)\.'

n_variables = len(re.findall(variable_regex, file))

uncommented_file = re.sub(comment_regex, '', file)
fields = re.search(record_regex, uncommented_file, re.DOTALL).group(2).split(record_sep)
field_names = [re.match(field_name_regex, field).group(1) for field in fields]

setters = ""
notations = ""
arguments = ""
variables = ' _' * n_variables

constructor_name = "mk" + record_name[0].upper() + record_name[1:]

for field_name in field_names:
    setters += "\n\nDefinition set_%s_%s a v := %s" % (record_name,field_name,constructor_name)
    for fn in field_names:
        if fn == field_name:
            setters += " v"
        else:
            setters += " (%s a)" % fn
    setters += "."

    notations += "\n\nNotation \"{[ a 'with' '%s' := v ]}\" := (set_%s_%s %s a v)." % (field_name, record_name,field_name,variables)
    arguments += "\n\nArguments set_%s_%s %s/." % (record_name, field_name, " _" * (n_variables + 2))

setters += "\n"

lines = file.split("\n")

print "\n".join(lines[:-2])
print setters
print "\n".join(lines[-2:])
print notations
print arguments
