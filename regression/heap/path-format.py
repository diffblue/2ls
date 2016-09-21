from lepl import Any, Delayed, Node, Space

expr = Delayed()
expr += '{' / (Any() | expr[1:, Space()[:]]) / '}' > Node

print expr.parse("{{a}{b}{{{c}}}}")[0]
