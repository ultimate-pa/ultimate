package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import parma_polyhedra_library.Coefficient;
import parma_polyhedra_library.Constraint;
import parma_polyhedra_library.Degenerate_Element;
import parma_polyhedra_library.Linear_Expression;
import parma_polyhedra_library.NNC_Polyhedron;
import parma_polyhedra_library.Variable;

public class PolytopeState implements IAbstractState<PolytopeState> {
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractState#hasVariable(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .AbstractVariable)
	 */
	@Override
	public boolean hasVariable(AbstractVariable variable) {
		return mVariableTranslation.getVariables().containsKey(variable);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractState#declareVariable(de
	 * .uni_freiburg.informatik.
	 * ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.TypedAbstractVariable)
	 */
	@Override
	public void declareVariable(TypedAbstractVariable variable) {
		if (variable.getDeclaration() == null && variable.getType() == null) {
			throw new RuntimeException();
		}
		Variable x = mVariableTranslation.addVariable(variable);
		updateDimensions();
		// mLogger.debug("Declare variable: " + variable.toString() +
		// " [value: " + x.toString() + "]");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractState#getTypedVariable(de
	 * .uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable)
	 */
	public TypedAbstractVariable getTypedVariable(AbstractVariable variable) {
		for (TypedAbstractVariable tav : mVariableTranslation.getVariables().keySet()) {
			if (tav.equals(variable)) {
				return tav;
			}
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractState#removeVariable(de.
	 * uni_freiburg.informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.AbstractVariable)
	 */
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractState#isSuper(de.uni_freiburg
	 * .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain
	 * .IAbstractState)
	 */
	@Override
	public boolean isSuperOrEqual(IAbstractState<PolytopeState> state) {
		if (state.isBottom()) {
			return true;
		}

		if (mIsBottom) {
			return false;
		}

		PolytopeState pState = state.getConcrete();

		synchroniseDimensions(pState);

		return mPolyhedron.contains(pState.mPolyhedron);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractState#copy()
	 */
	@Override
	public PolytopeState copy() {
		PolytopeState copy = new PolytopeState(mLogger);
		copy.mIsBottom = mIsBottom;
		copy.mPolyhedron = new NNC_Polyhedron(mPolyhedron);
		copy.mVariableTranslation = mVariableTranslation;
		return copy;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractState#isBottom()
	 */
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
	 * Checkse whether this polytope is the universal poytope (no constraints)
	 * 
	 * @return
	 */
	public boolean isTop() {
		return mPolyhedron.is_universe();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractState#getConcrete()
	 */
	@Override
	public PolytopeState getConcrete() {
		return this;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
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
}
