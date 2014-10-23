package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler;

import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTypedefNameSpecifier;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * TypeHandler for SVComp -- supposed to deal with GNU C specific stuff like builtin types and so..
 * @author alex
 *
 */
public class SVCompTypeHandler extends TypeHandler {
    @Override
    public Result visit(Dispatcher main, IASTNamedTypeSpecifier node) {
        ILocation loc = LocationFactory.createCLocation(node);
        if (node instanceof CASTTypedefNameSpecifier) {
            node = (CASTTypedefNameSpecifier) node;
            String cId = node.getName().toString();
            
            // quick solution --> TODO: maybe make this dependent on includes, 
            // maybe be more elegant (make an entry to symboltable, make a typedef in boogie file??)
            if (cId.equals("size_t") || cId.equals("ssize_t")) {
                return (new ResultTypes(new PrimitiveType(loc, SFO.REAL), node.isConst(),
                		false, new CPrimitive(PRIMITIVE.UINT)));
            } else if (cId.equals("__builtin_va_list")) {
                return (new ResultTypes(MemoryHandler.POINTER_TYPE, node.isConst(),
                		false, new CPointer(new CPrimitive(PRIMITIVE.CHAR))));
            } else if (cId.equals("__pthread_list_t")) {
            	    return (new ResultTypes(MemoryHandler.POINTER_TYPE, node.isConst(),
                		false, new CPointer(new CPrimitive(PRIMITIVE.VOID))));
            } else {
            	return super.visit(main, node);
            }
        }
        String msg = "Unknown or unsupported type! " + node.toString();
        throw new UnsupportedSyntaxException(loc, msg);
    }
}
