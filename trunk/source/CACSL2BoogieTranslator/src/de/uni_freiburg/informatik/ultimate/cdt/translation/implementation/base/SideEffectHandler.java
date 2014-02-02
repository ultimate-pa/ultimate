/**
 * An example implementation for a side effect handler.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ISideEffectHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
public class SideEffectHandler implements ISideEffectHandler {

    @Override
    public Result visit(Dispatcher main, IASTNode node) {
        String msg = "SideEffectHandler: Not yet implemented: "
                + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, ACSLNode node) {
        String msg = "SideEffectHandler: Not yet implemented: "
                + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        throw new UnsupportedSyntaxException(msg);
    }
}
