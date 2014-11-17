package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark the
 * root node so various tools knows that they should run in LTL mode and which
 * property should be checked.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */

public class LTLPropertyCheck extends Check {

	private static final long serialVersionUID = 1L;
	private static final String sKey = LTLPropertyCheck.class.getSimpleName();
	private static final String[] sFieldNames = new String[] { "Check", "UseLTLMode", "LTL Property" };

	private final String mLTLProptery;
	private final Map<String, CheckableExpression> mCheckableAtomicPropositions;
	private final List<VariableDeclaration> mGlobalDeclarations;

	public LTLPropertyCheck(String ltlPropertyAsString, Map<String, CheckableExpression> checkableAtomicPropositions,
			List<VariableDeclaration> globalDeclarations) {
		super(Spec.LTL);
		mLTLProptery = ltlPropertyAsString;
		mCheckableAtomicPropositions = checkableAtomicPropositions;
		mGlobalDeclarations = globalDeclarations;
	}

	public String getLTLProperty() {
		return mLTLProptery;
	}

	@Override
	public String getNegativeMessage() {
		return "The LTL property " + mLTLProptery + " was violated.";
	}

	@Override
	public String getPositiveMessage() {
		return "The LTL property " + mLTLProptery + " holds.";
	}

	@Override
	protected String[] getFieldNames() {
		return sFieldNames;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field.equals(sFieldNames[0])) {
			return getSpec().toString();
		} else if (field.equals(sFieldNames[1])) {
			return true;
		} else if (field.equals(sFieldNames[2])) {
			return getLTLProperty();
		} else {
			return null;
		}
	}

	public void annotate(IElement elem) {
		elem.getPayload().getAnnotations().put(sKey, this);
	}

	public static LTLPropertyCheck getAnnotation(IElement elem) {
		if (!elem.hasPayload()) {
			return null;
		}
		if (!elem.getPayload().hasAnnotation()) {
			return null;
		}
		return (LTLPropertyCheck) elem.getPayload().getAnnotations().get(sKey);
	}

	/**
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 * 
	 */
	public class CheckableExpression {
		private final Expression mExpression;
		private final List<Statement> mStatements;

		public CheckableExpression(Expression expr, List<Statement> statements) {
			mExpression = expr;
			mStatements = statements;
		}

		public Expression getExpression() {
			return mExpression;
		}

		public List<Statement> getStatements() {
			return mStatements;
		}

	}

}
