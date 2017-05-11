package de.uni_freiburg.informatik.ultimate.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class BoogieBacktranslationValueProvider implements IBacktranslationValueProvider<BoogieASTNode, Expression> {

	@Override
	public int getStartLineNumberFromStep(final BoogieASTNode step) {
		if (step.getLocation() == null) {
			return -1;
		}
		return step.getLocation().getStartLine();
	}

	@Override
	public int getEndLineNumberFromStep(final BoogieASTNode step) {
		if (step.getLocation() == null) {
			return -1;
		}
		return step.getLocation().getEndLine();
	}

	@Override
	public String getOriginFileNameFromStep(final BoogieASTNode step) {
		final ILocation loc = step.getLocation();
		if (loc == null) {
			return null;
		}
		return loc.getFileName();
	}

	@Override
	public String getStringFromStep(final BoogieASTNode step) {
		if (step instanceof Statement) {
			return BoogiePrettyPrinter.print((Statement) step);
		} else if (step instanceof Specification) {
			return BoogiePrettyPrinter.print((Specification) step);
		} else if (step instanceof Expression) {
			return BoogiePrettyPrinter.print((Expression) step);
		} else {
			throw new IllegalArgumentException("current step is neither Statement nor Specification nor Expression");
		}
	}

	@Override
	public String getStringFromTraceElement(final BoogieASTNode traceelement) {
		return getStringFromStep(traceelement);
	}

	@Override
	public String getStringFromExpression(final Expression expression) {
		return BoogiePrettyPrinter.print(expression);
	}

	@Override
	public String getFileNameFromStep(final BoogieASTNode step) {
		return step.getLocation().getFileName();
	}

}