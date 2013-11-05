package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;

public class SvComp14TypeHandler extends TypeHandler {

	@Override
	public Result visit(Dispatcher main, IASTElaboratedTypeSpecifier node) {
		// ignore structs in svcomp mode
		if (node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
			return new ResultSkip();
		} else {
			return super.visit(main, node);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTCompositeTypeSpecifier node) {
		// ignore structs in svcomp mode
		if (node.getKey() == IASTElaboratedTypeSpecifier.k_union) {
			return new ResultSkip();
		} else {
			return super.visit(main, node);
		}
	}

}
