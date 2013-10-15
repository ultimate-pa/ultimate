package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;

/**
 * @author Markus Lindenmann
 * @date 21.10.2012
 */
public class SVCompTypeHandler extends TypeHandler {
    @Override
    public Result visit(Dispatcher main, IASTElaboratedTypeSpecifier node) {
//        if (node.getKind() != IASTElaboratedTypeSpecifier.k_struct) {
//            return new ResultSkip();
//        }
        return super.visit(main, node);
    }
}
