/*
 * 
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * AssertionError in MemoryHandler:
 * assert cvar != null;
 * 
 * Reason in TypeHandler:
 * ResultTypes r = new ResultTypes(new NamedType(loc, name, ASTType[0]),
 *                                 false, false, null);
 * // FIXME : not sure, if null is a good idea!
 */
struct list;

int func(struct list *l) {
    return 0;
}

int main() {
    return 0;
}
