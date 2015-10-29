package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import org.apache.log4j.Logger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import parma_polyhedra_library.Coefficient;
import parma_polyhedra_library.Constraint;
import parma_polyhedra_library.Degenerate_Element;
import parma_polyhedra_library.Linear_Expression;
import parma_polyhedra_library.NNC_Polyhedron;
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
		return mVariableTranslation.getVariables().containsKey(variable);
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
		for (TypedAbstractVariable tav : mVariableTranslation.getVariables().keySet()) {
			if (tav.equals(variable)) {
				return tav;
			}
		}
		return null;
	}

	@Override
	public void removeVariable(AbstractVariable variable) {
		updateDimensions();
		// TODO: remove all related constrains from the polyhedron
		// mLogger.debug("Remove variable: " + variable.toString() +
		// " (implementation not finished)");
		mVariableTranslation.getVariables().remove(variable);
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
		return mVariableTranslation.getVariables().get(variable);
	}

	/**
	 * Make sure that the polytope has the correct number of dimensions
	 * 
	 * @param pState
	 */
	public void updateDimensions() {
		int missingDimensions = mVariableTranslation.nofVariables() - (int) mPolyhedron.space_dimension();
		if (missingDimensions > 0) {
			mPolyhedron.add_space_dimensions_and_embed(missingDimensions);
		} else if (missingDimensions < 0) {
			// too many dimensions
			throw new UnsupportedOperationException();
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
		if (mVariableTranslation != state.mVariableTranslation) {
			if (mVariableTranslation.union(state.mVariableTranslation)) {
				// mLogger.debug("Uniting tables of " + this.toString());
				state.mVariableTranslation = mVariableTranslation;
			} else {
				// fold the dimensions of one poytope to match the table of the
				// other state
				throw new RuntimeException("The two states must have the same variable tanslation");
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
		// mLogger.debug("Adding Constraint: " + constraint.toString());
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
		// for(Constraint con : mPolyhedron.constraints()){
		// con.
		// }
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Minimizes the polyhedron representation.
	 */
	protected void minimize() {
		mPolyhedron = new NNC_Polyhedron(mPolyhedron.minimized_generators());
	}
}
