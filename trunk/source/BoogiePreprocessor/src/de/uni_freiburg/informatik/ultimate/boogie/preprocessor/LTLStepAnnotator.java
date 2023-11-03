package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;

import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LTLStepAnnotation;

/**
 * Transform Boogie annotations of the form {: ltl_step } into corresponding
 * step specifications.
 *
 * @author Martin Neuhäußer (post@marneu.com)
 */
public class LTLStepAnnotator extends BaseObserver {

	protected LTLStepAnnotator() {
	}

	/**
	 * The process function. Called by the tool-chain and gets a node of the graph as parameter.
	 * The function traverses the graph and attached LTL step specifications to each assume,
	 * assert and call statement that has an "ltl_step" attribute attached to it.
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			processUnit(unit);
			return false;
		}
		return true;
	}

	/**
	 * Searches for all procedures in the Boogie file and visits each statement.
	 * @param unit The root of the abstract syntax tree
	 */
	private void processUnit(final Unit unit) {
		final BoogieLTLStepAnnotator ltlAnnotator = new BoogieLTLStepAnnotator();
		unit.accept(ltlAnnotator);
	}

	/**
	 * Attach LTL step specifications to all assume, assert and call statements that have
	 * a Boogie attribute "ltl_step" attached to them.
	 * @author Martin Neuhäußer
	 */
	private final class BoogieLTLStepAnnotator extends GeneratedBoogieAstTransformer {
		private Statement attachLTLSpecification(final Statement stmt, final NamedAttribute[] attrs) {
			if (attrs != null) {
				for (final NamedAttribute attr : attrs) {
					if (attr.getName() == "ltl_step") {
						LTLStepAnnotation stepAnnotation = new LTLStepAnnotation();
						stepAnnotation.annotate(stmt);
					}
				}
			}
			return stmt;
		}

		@Override
		public Statement transform(final AssumeStatement node) {
			return attachLTLSpecification(node, node.getAttributes());
		}

		@Override
		public Statement transform(final AssertStatement node) {
			return attachLTLSpecification(node, node.getAttributes());
		}

		@Override
		public Statement transform(final CallStatement node) {
			return attachLTLSpecification(node, node.getAttributes());
		}

	}
}
