package de.uni_freiburg.informatik.ultimate.cookiefy;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;

/**
 * Contains all context path related operations
 * 
 * @author Jeremi, Vincent
 * 
 */
public class ContextPath {
	public enum FormulaType {
		Alpha, And, Or, AF, AW, AG
	}

	static public class ContextPathNode {
		private FormulaType m_FormulaType;
		private String m_Path;

		public FormulaType getFormulaType() {
			return this.m_FormulaType;
		}

		public String getPath() {
			return this.m_Path;
		}

		public ContextPathNode(FormulaType type, String path) {
			this.m_FormulaType = type;
			this.m_Path = path;
		}

		/**
		 * returns true, if FormulaType is AG, AF or AW
		 * 
		 * @return
		 */
		public boolean isTemporal() {
			if (this.m_FormulaType == FormulaType.AF)
				return true;
			if (this.m_FormulaType == FormulaType.AG)
				return true;
			if (this.m_FormulaType == FormulaType.AW)
				return true;
			return false;
		}

		public boolean isAtom() {
			if (this.m_FormulaType == FormulaType.Alpha)
				return true;
			return false;
		}
		
		@Override
		public String toString() {
			return getPath();
		}
	}

	static public class ContextPathAlphaNode extends ContextPathNode {
		private Expression m_Expression;

		public Expression getExpression() {
			return this.m_Expression;
		}

		public ContextPathAlphaNode(String path, Expression content) {
			super(FormulaType.Alpha, path);
			this.m_Expression = content;
		}
	}

	// TODO: write 'Sub'-Function
	// static ContextPathNode[] Sub(...) {
	// }

	static ContextPathNode[] getCollantExampleSubResult() {
		return new ContextPathNode[] {
				new ContextPathNode(FormulaType.AG, "T"),
				new ContextPathNode(FormulaType.Or, "TL"),
				new ContextPathAlphaNode("TLL", new UnaryExpression(
						LocationProvider.getLocation(),
						UnaryExpression.Operator.LOGICNEG,
						new IdentifierExpression(
								LocationProvider.getLocation(), "warn"))),
				new ContextPathNode(FormulaType.AW, "TLR"),
				new ContextPathAlphaNode("TLRL", new IdentifierExpression(
						LocationProvider.getLocation(), "warn")),
				new ContextPathNode(FormulaType.And, "TLRR"),
				new ContextPathAlphaNode("TLRLL", new UnaryExpression(
						LocationProvider.getLocation(),
						UnaryExpression.Operator.LOGICNEG,
						new IdentifierExpression(
								LocationProvider.getLocation(), "warn"))),
				new ContextPathNode(FormulaType.AG, "TLRRR"),
				new ContextPathAlphaNode("TLRRRL", new IdentifierExpression(
						LocationProvider.getLocation(), "mad")) };
	}

	static ContextPathNode[] getExampleSubResult() {
		return new ContextPathNode[] {
				new ContextPathNode(FormulaType.AG, "T"),
				new ContextPathNode(FormulaType.Or, "TL"),
				new ContextPathAlphaNode("TLL", new BooleanLiteral(
						LocationProvider.getLocation(), true)),
				new ContextPathNode(FormulaType.AW, "TLR"),
				new ContextPathAlphaNode("TLRL", new BooleanLiteral(
						LocationProvider.getLocation(), false)),
				new ContextPathAlphaNode("TLRR", new BooleanLiteral(
						LocationProvider.getLocation(), false)) };
	}

	static ContextPathNode[] getExampleSubResult2() {
		return new ContextPathNode[] {
				new ContextPathNode(FormulaType.AG, "T"),
				new ContextPathAlphaNode("TL", new BooleanLiteral(
						LocationProvider.getLocation(), true)) };
	}

	static ContextPathNode[] getAGNotFoo() {
		return new ContextPathNode[] {
				new ContextPathNode(FormulaType.AG, "T"),
				new ContextPathAlphaNode("TL", new UnaryExpression(
						LocationProvider.getLocation(),
						UnaryExpression.Operator.LOGICNEG,
						new IdentifierExpression(
								LocationProvider.getLocation(), "foo"))) };
	}
}
