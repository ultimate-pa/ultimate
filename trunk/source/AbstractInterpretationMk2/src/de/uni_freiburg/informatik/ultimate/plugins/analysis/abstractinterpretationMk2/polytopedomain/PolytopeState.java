package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import parma_polyhedra_library.Coefficient;
import parma_polyhedra_library.Constraint;
import parma_polyhedra_library.Degenerate_Element;
import parma_polyhedra_library.Linear_Expression;
import parma_polyhedra_library.Linear_Expression_Coefficient;
import parma_polyhedra_library.Linear_Expression_Difference;
import parma_polyhedra_library.Linear_Expression_Sum;
import parma_polyhedra_library.Linear_Expression_Times;
import parma_polyhedra_library.Linear_Expression_Unary_Minus;
import parma_polyhedra_library.Linear_Expression_Variable;
import parma_polyhedra_library.NNC_Polyhedron;
import parma_polyhedra_library.Partial_Function;
import parma_polyhedra_library.Relation_Symbol;
import parma_polyhedra_library.Variable;

/**
 * 
 * @author Jan Hättig
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PolytopeState implements IAbstractState<PolytopeState> {

	private static final long MAX_MEMORY = (long) (Runtime.getRuntime().maxMemory() * 0.2);

	/**
	 * Logger for debug output
	 */
	private final Logger mLogger;

	/**
	 * If this is true, the polytope is to be considered bottom. No matter what
	 * its internal state is
	 */
	private boolean mIsBottom;

	/**
	 * The actual polytope
	 */
	private NNC_Polyhedron mPolyhedron;

	/**
	 * ID for debugging
	 */
	private final int mUID;

	private static int sNextUID = 0;

	private VariableTranslation mVariableTranslation;

	/**
	 * Constructor
	 * 
	 * @param logger
	 */
	public PolytopeState(Logger logger) {
		mLogger = logger;
		mIsBottom = false;
		mPolyhedron = new NNC_Polyhedron(0, Degenerate_Element.UNIVERSE);
		mVariableTranslation = new VariableTranslation();
		mUID = sNextUID++;
	}

	private PolytopeState(PolytopeState old) {
		mLogger = old.mLogger;
		mIsBottom = old.mIsBottom;
		mPolyhedron = new NNC_Polyhedron(old.mPolyhedron);
		mVariableTranslation = old.mVariableTranslation;
		mUID = sNextUID++;
	}

	@Override
	public boolean hasVariable(AbstractVariable variable) {
		return getTypedVariable(variable) != null;
	}

	@Override
	public void declareVariable(TypedAbstractVariable variable) {
		if (variable.getDeclaration() == null && variable.getType() == null) {
			throw new RuntimeException();
		}
		mVariableTranslation.addVariable(variable);
		updateDimensions();
		// mLogger.debug("Declare variable: " + variable.toString() +
		// " [value: " + x.toString() + "]");
	}

	public TypedAbstractVariable getTypedVariable(AbstractVariable variable) {
		return mVariableTranslation.checkVar(variable);
	}

	@Override
	public void removeVariable(AbstractVariable variable) {
		updateDimensions();
		// TODO: remove all related constrains from the polyhedron
		// mLogger.debug("Remove variable: " + variable.toString() +
		// " (implementation not finished)");
		mVariableTranslation.removeVariable((TypedAbstractVariable) variable);
		throw new UnsupportedOperationException();
	}

	/**
	 * Does that the given variable is equivalent to the given expression. But
	 * every thing else stays the same
	 * 
	 * @param target
	 */
	public void writeVariable(AbstractVariable target, Linear_Expression expr) {
		updateDimensions();
		Variable var = getVariable(target);
		// mLogger.debug("Write Variable (" + target + "): " + var.toString() +
		// " := " + expr.toString());
		mPolyhedron.affine_image(var, expr, new Coefficient(1));
	}

	/**
	 * Does that the given variable has an unbound range. But every thing else
	 * stays the same
	 * 
	 * @param target
	 */
	public void havocVariable(TypedAbstractVariable target) {
		updateDimensions();
		Variable var = getVariable(target);
		// mLogger.debug("Havoc Variable (" + target + "): " + var.toString());
		mPolyhedron.unconstrain_space_dimension(var);
	}

	/**
	 * Returns the polyhedron's variable for a given variable
	 * 
	 * @param variable
	 * @return
	 */
	public Variable getVariable(AbstractVariable variable) {
		return mVariableTranslation.getPPLVar(variable);
	}

	/**
	 * Make sure that the polytope has the correct number of dimensions
	 * 
	 * @param pState
	 */
	public void updateDimensions() {
		long needed = mVariableTranslation.size();
		long existing = mPolyhedron.space_dimension();
		long missingDimensions = needed - existing;
		if (missingDimensions > 0) {
			mPolyhedron.add_space_dimensions_and_embed(missingDimensions);
		} else if (missingDimensions < 0) {
			// too many dimensions
			mLogger.warn("Poly has " + existing + " but we need only " + needed);
		}
	}

	/**
	 * Ensures, that this state has the same dimensions as the other and
	 * synchronizes both polytopes
	 * 
	 * @param state
	 */
	public void synchroniseDimensions(PolytopeState state) {
		// the two polytopes must be of the same scope
		// and hence have the same variable translation instance
		if (mVariableTranslation != state.mVariableTranslation) 
		{			
			if (mVariableTranslation.union(state.mVariableTranslation)) {
				// mLogger.debug("Uniting tables of " + this.toString());
				mVariableTranslation = state.mVariableTranslation;
			} else {
				// fold the dimensions of one polytope to match the table of the
				// other state
				// make a copy
				mVariableTranslation = new VariableTranslation(mVariableTranslation);
				mLogger.debug("asdf_: " + mPolyhedron.space_dimension());
				mLogger.debug("before remap: " + mVariableTranslation.toString());
				mLogger.debug("other: " + state.mVariableTranslation.toString());
				Partial_Function mapping = mVariableTranslation.remap(state.mVariableTranslation, mLogger);				
				mLogger.debug("after remap: " + mVariableTranslation.toString());

				updateDimensions();
				//mPolyhedron.add_space_dimensions_and_embed(1);
				mLogger.debug("asdf_: " + mPolyhedron.space_dimension());
				
				mPolyhedron.map_space_dimensions(mapping);
				// now try again
				if (mVariableTranslation.union(state.mVariableTranslation)) {
					// mLogger.debug("Uniting tables of " + this.toString());
					mVariableTranslation = state.mVariableTranslation;
				} else {
					throw new RuntimeException("The two states must have the same variable tanslation");
				}
			}
		}
		updateDimensions();
		
		state.updateDimensions();
	}

	/**
	 * Adds a constraint to the polyhedron
	 * 
	 * @param constraint
	 */
	public void addConstraint(Constraint constraint) {
		updateDimensions();
		mLogger.debug("Adding Constraint: " + constraint.toString());
		mPolyhedron.add_constraint(constraint);
	}

	@Override
	public boolean isSuperOrEqual(IAbstractState<?> state) {
		if (state.isBottom()) {
			return true;
		}

		if (mIsBottom) {
			return false;
		}

		if (!(state instanceof PolytopeState)) {
			return false;
		}

		final PolytopeState pState = (PolytopeState) state;
		synchroniseDimensions(pState);

		return mPolyhedron.contains(pState.mPolyhedron);
	}

	@Override
	public PolytopeState copy() {
		if (mPolyhedron.external_memory_in_bytes() > MAX_MEMORY) {
			throw new OutOfMemoryError("Not enough heap space available to represent the polyhedron.");
		}
		return new PolytopeState(this);
	}

	@Override
	public boolean isBottom() {
		if (mIsBottom || mPolyhedron.is_empty()) {
			mIsBottom = true;
			return true;
		}
		return false;
	}

	/**
	 * Makes this a bottom state. Cannot be undone
	 */
	public void setIsBottom() {
		mIsBottom = true;
	}

	/**
	 * Checks whether this polytope is the universal polytope (no constraints)
	 * 
	 * @return
	 */
	public boolean isTop() {
		return mPolyhedron.is_universe();
	}

	@Override
	public PolytopeState getConcrete() {
		return this;
	}

	@Override
	public String toString() {
		String output = "[UID_" + mUID + " ";
		output += mVariableTranslation.toString() + " ";
		return output
				// + "pObj(" + mPolyhedron.space_dimension() + "): "
				+ mPolyhedron.toString() + "]";
	}

	public NNC_Polyhedron getPolytope() {
		return mPolyhedron;
	}

	/**
	 * Used for concatenating and un-concatenating
	 * 
	 * @return
	 */
	public VariableTranslation getVariableTranslation() {
		return mVariableTranslation;
	}

	/**
	 * Used for concatenating and un-concatenating
	 * 
	 * @return
	 */
	public void setVariableTranslation(VariableTranslation variableTranslation) {
		mVariableTranslation = variableTranslation;
	}

	@Override
	public Term getTerm(Script script, Boogie2SMT bpl2smt) {
		if (isBottom()) {
			return script.term("false");
		}

		final ConstraintWalker cwalker = new ConstraintWalker(script, bpl2smt, mVariableTranslation);
		Term acc = script.term("true");
		for (final Constraint con : mPolyhedron.constraints()) {
			try {
				final Term left = cwalker.process(con.left_hand_side());
				final Term right = cwalker.process(con.right_hand_side());
				final Relation_Symbol kind = con.kind();
				final String op;

				switch (kind) {
				case EQUAL:
					op = "=";
					break;
				case GREATER_OR_EQUAL:
					op = ">=";
					break;
				case GREATER_THAN:
					op = ">";
					break;
				case LESS_OR_EQUAL:
					op = "<=";
					break;
				case LESS_THAN:
					op = "<";
					break;
				case NOT_EQUAL:
					op = "!=";
					break;
				default:
					throw new UnsupportedOperationException("Unknown \"kind\" of constraint: " + kind);
				}

				acc = script.term("and", acc, script.term(op, left, right));
			} catch (IgnoreTermException ex) {
				// we really just ignore the term
				mLogger.warn("We do not support constraints over arrays: " + con);
			}
		}

		return acc;
	}

	private static final class ConstraintWalker {
		private final Boogie2SMT mBoogie2SMT;
		private final Script mScript;
		private final VariableTranslation mTrans;

		private ConstraintWalker(final Script script, final Boogie2SMT bpl2smt, final VariableTranslation trans) {
			mScript = script;
			mBoogie2SMT = bpl2smt;
			mTrans = trans;
		}

		private Term process(final Linear_Expression expr) throws IgnoreTermException {
			if (expr instanceof Linear_Expression_Coefficient) {
				return process((Linear_Expression_Coefficient) expr);
			} else if (expr instanceof Linear_Expression_Difference) {
				return process((Linear_Expression_Difference) expr);
			} else if (expr instanceof Linear_Expression_Sum) {
				return process((Linear_Expression_Sum) expr);
			} else if (expr instanceof Linear_Expression_Times) {
				return process((Linear_Expression_Times) expr);
			} else if (expr instanceof Linear_Expression_Unary_Minus) {
				return process((Linear_Expression_Unary_Minus) expr);
			} else if (expr instanceof Linear_Expression_Variable) {
				return process((Linear_Expression_Variable) expr);
			} else {
				throw new UnsupportedOperationException("Dont know " + (expr == null ? "null" : expr.ascii_dump()));
			}
		}

		private Term process(final Linear_Expression_Coefficient expr) {
			return process(expr.argument());
		}

		private Term process(final Linear_Expression_Times expr) throws IgnoreTermException {
			final Term coeff = process(expr.coefficient());
			final Term inner = process(expr.linear_expression());
			return mScript.term("*", coeff, inner);
		}

		private Term process(final Coefficient expr) {
			return mScript.numeral(expr.getBigInteger());
		}

		private Term process(final Linear_Expression_Difference expr) throws IgnoreTermException {
			final Term left = process(expr.left_hand_side());
			final Term right = process(expr.right_hand_side());
			return mScript.term("-", left, right);
		}

		private Term process(final Linear_Expression_Sum expr) throws IgnoreTermException {
			final Term left = process(expr.left_hand_side());
			final Term right = process(expr.right_hand_side());
			return mScript.term("+", left, right);
		}

		private Term process(final Linear_Expression_Unary_Minus expr) throws IgnoreTermException {
			final Term arg = process(expr.argument());
			return mScript.term("-", arg);
		}

		private Term process(final Linear_Expression_Variable expr) throws IgnoreTermException {
			final Variable arg = expr.argument();
			final TypedAbstractVariable var = mTrans.getVar(arg);
			assert var != null : "Unknown variable in constraint";
			final Term termvar = var.getTermVar(mBoogie2SMT);
			final Sort sort = termvar.getSort().getRealSort();
			if (!sort.getName().equals("Int")) {
				//ignore array sorts for now
				throw new IgnoreTermException();
			}
			return termvar;
		}
	}

	private static final class IgnoreTermException extends Exception {
		private static final long serialVersionUID = 1L;
	}

	/**
	 * Minimizes the polyhedron representation.
	 */
	protected void minimize() {
		mPolyhedron = new NNC_Polyhedron(mPolyhedron.minimized_generators());
	}
}
