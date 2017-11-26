package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * TODO: this class seems entirely useless and can be replaced by ExpressionResult -- should do this during a cleanup
 *  (or remove deprecated annotation if a use shows up where ExpressionResult cannot be used)
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
@Deprecated
public class CompoundStatementExpressionResult extends ExpressionResult {

	public CompoundStatementExpressionResult(final ArrayList<Statement> stmt, final LRValue lrVal, final ArrayList<Declaration> decl,
			final Map<VariableDeclaration, ILocation> auxVars, final List<Overapprox> overapproxList) {
		super(stmt, lrVal, decl, auxVars, overapproxList);
	}
}
