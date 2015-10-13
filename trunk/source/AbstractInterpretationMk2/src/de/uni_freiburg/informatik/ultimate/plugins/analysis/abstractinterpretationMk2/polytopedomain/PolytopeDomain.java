/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractWideningOperator;
import parma_polyhedra_library.Constraint;
import parma_polyhedra_library.Linear_Expression;
import parma_polyhedra_library.Linear_Expression_Variable;
import parma_polyhedra_library.NNC_Polyhedron;
import parma_polyhedra_library.Parma_Polyhedra_Library;
import parma_polyhedra_library.Relation_Symbol;
import parma_polyhedra_library.Variable;

/**
 * Implements the polytope domain
 * 
 * @author Jan H�ttig
 *
 */
public class PolytopeDomain implements IAbstractDomain<PolytopeState> {
	/**
	 * String representing this domain
	 */
	private static final String s_domainID = "POLYTOPE";

	/**
	 * The logger object
	 */
	private final Logger mLogger;

	/**
	 * The merge operator which is used for this domain.
	 */
	private IAbstractMergeOperator<PolytopeState> mMergeOperator;
	/**
	 * The widening operator which is used for this domain.
	 */
	private IAbstractWideningOperator<PolytopeState> mWideningOperator;

	/**
	 * for applying expressions
	 */
	private final PolytopeAssumptionVisitor mAssumptionVisitor;

	/**
	 * for applying assignments
	 */
	private final PolytopeExpressionVisitor mExpressionVisitor;

	private static boolean sParmaLibraryInitialized = false;

	/**
	 * Constructor
	 * 
	 * @param logger
	 */
	public PolytopeDomain(Logger logger) {
		if (!sParmaLibraryInitialized) {
			try {
				// because of OSGi, we have to load all dependent libraries
				// manually
				// the order is important (!)
				switch (System.getProperty("os.name")) {
				case "Linux":
					System.loadLibrary("gmp"); // libgmp version >= 10 is needed.
					System.loadLibrary("gmpxx"); // libgmpxx version >= 4 is needed.
					System.loadLibrary("ppl"); // libppl version >= 13 is needed. 
					break;
				case "Windows":
					System.loadLibrary("libgmp-10");
					System.loadLibrary("libwinpthread-1");
					System.loadLibrary("libgcc_s_seh-1");
					System.loadLibrary("libstdc++-6");
					System.loadLibrary("libgmpxx-4");
					System.loadLibrary("libppl-13");
					break;
				default:
					throw new UnsatisfiedLinkError(
					        "The operating system \"" + System.getProperty("os.name") + "\" is not supported.");
				}

				// now we load the real deal
				System.loadLibrary("ppl_java");

				logger.info("Loaded PPL");
			} catch (UnsatisfiedLinkError e) {
				final String errorMsg = "Unable to load PPL: " + e.getMessage();
				logger.fatal(errorMsg);
				logger.fatal(e);
				throw new RuntimeException(errorMsg, e);
			}

			logger.info("Parma-Library: Initializing (Version" + Parma_Polyhedra_Library.version() + ")");
			Parma_Polyhedra_Library.initialize_library();
			sParmaLibraryInitialized = true;
		}
		mLogger = logger;
		mExpressionVisitor = new PolytopeExpressionVisitor(logger);
		mAssumptionVisitor = new PolytopeAssumptionVisitor(mExpressionVisitor, logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#getMergeOperator()
	 */
	@Override
	public IAbstractMergeOperator<PolytopeState> getMergeOperator() {
		return mMergeOperator;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#getWideningOperator()
	 */
	@Override
	public IAbstractWideningOperator<PolytopeState> getWideningOperator() {
		return mWideningOperator;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#setMergeOperator( de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractMergeOperator)
	 */
	@Override
	public void setMergeOperator(IAbstractMergeOperator<PolytopeState> mergeOperator) {
		mMergeOperator = mergeOperator;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#setWideningOperator (de.uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractWideningOperator)
	 */
	@Override
	public void setWideningOperator(IAbstractWideningOperator<PolytopeState> wideningOperator) {
		mWideningOperator = wideningOperator;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.IAbstractDomain#createState()
	 */
	@Override
	public IAbstractState<PolytopeState> createState() {
		return new PolytopeState(mLogger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyExpression(de .uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2 .abstractdomain.IAbstractState,
	 * de.uni_freiburg.informatik.ultimate.plugins
	 * .analysis.abstractinterpretationMk2.abstractdomain.TypedAbstractVariable,
	 * de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression)
	 */
	@Override
	public IAbstractState<PolytopeState> applyExpression(IAbstractState<PolytopeState> state,
	        TypedAbstractVariable target, Expression exp) {
		return applyExpression(state, target, exp, "");
	}

	/**
	 * Manifesting the expression in state with the given target variable
	 * 
	 * @param prefix
	 *            this prefix will be to each variable in the given expression
	 */
	public IAbstractState<PolytopeState> applyExpression(IAbstractState<PolytopeState> state,
	        TypedAbstractVariable target, Expression exp, String prefix) {
		PolytopeState pState = (PolytopeState) state;

		mExpressionVisitor.prepare(pState, prefix);
		Linear_Expression right = null;
		IAbstractState<PolytopeState> stateCopy = null;
		if (exp instanceof ArrayStoreExpression) {
			stateCopy = state.copy();
			ArrayStoreExpression ase = (ArrayStoreExpression) exp;
			right = mExpressionVisitor.walk(ase.getValue());

			// TODO: do something better with arrays
			// like creating a 2D-polytope as value representation
		} else {
			right = mExpressionVisitor.walk(exp);
		}

		if (right == null) {
			// If we cannot process the expression, we assume
			// we know nothing about the target variable
			// mLogger.debug("Cannot create ppl expression for: " +
			// exp.toString());
			return applyHavoc(state, target);
		}

		// it does not matter if the variable is already defined or not
		// in any case we define a new dimension for it
		// if it was already present the old variable will remain as a
		// dimension
		// TODO: Remove dimensions with no effect
		// pState.declareVariable(target);

		if (!pState.hasVariable(target)) {
			// declare the variable anew
			pState.declareVariable(target);
			Variable var = pState.getVariable(target);

			// Put it into to the polytope
			pState.addConstraint(new Constraint(new Linear_Expression_Variable(var), Relation_Symbol.EQUAL, right));
		} else {
			// the old value must be renamed such that
			// all relations keep being correct and a new one must
			// be introduced but with the same name
			pState.writeVariable(target, right);

			// For Arrays we only increase the state
			// (since the
			if (exp instanceof ArrayStoreExpression) {
				return mMergeOperator.apply(pState, stateCopy);
			}
		}

		return pState;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyHavoc(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractState,
	 * de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2.abstractdomain.TypedAbstractVariable)
	 */
	@Override
	public IAbstractState<PolytopeState> applyHavoc(IAbstractState<PolytopeState> state, TypedAbstractVariable target) {
		if (state.hasVariable(target)) {
			((PolytopeState) state).havocVariable(target);
		} else {
			state.declareVariable(target);
		}
		return state;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyAssume(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractState,
	 * de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression)
	 */
	@Override
	public List<IAbstractState<PolytopeState>> applyAssume(IAbstractState<PolytopeState> state, Expression expr) {
		List<PolytopeState> states = new ArrayList<PolytopeState>();
		states.add(state.getConcrete());
		List<PolytopeState> resultingState = mAssumptionVisitor.applyAssumption(expr, states, false);

		List<IAbstractState<PolytopeState>> result = new ArrayList<IAbstractState<PolytopeState>>();
		for (PolytopeState s : resultingState) {
			if (s == null) {
				throw new RuntimeException("States may not be null here");
			}

			s.updateDimensions();
			// the state was manipulated by the assumption walker
			result.add(s);
		}

		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyAssert(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractState,
	 * de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression)
	 */
	@Override
	public boolean checkAssert(IAbstractState<PolytopeState> state, Expression exp) {
		mLogger.warn("PolytopeDomain: ApplyAssert not implemented");

		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomain#ApplyCall(de.uni_freiburg .informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.abstractdomain .IAbstractState,
	 * de.uni_freiburg.informatik.ultimate.plugins.analysis. abstractinterpretationMk2.abstractdomain.IAbstractState,
	 * java.util.List, java.util.List)
	 */
	@Override
	public void applyExpressionScoped(IAbstractState<PolytopeState> targetState, IAbstractState<PolytopeState> oldState,
	        List<TypedAbstractVariable> targetVariables, List<Expression> arguments) {
		// concrete states
		PolytopeState target = targetState.getConcrete();
		PolytopeState old = oldState.getConcrete();

		// the polyhedron objects
		NNC_Polyhedron pTarget = target.getPolytope();
		NNC_Polyhedron pOld = old.getPolytope();

		// variable translation must be adjusted
		VariableTranslation vtTarget = target.getVariableTranslation();
		VariableTranslation vtOld = old.getVariableTranslation();

		// make shure that all variablels of targetVariables are declared in
		// vtTarget
		for (TypedAbstractVariable targetVariable : targetVariables) {
			if (!target.hasVariable(targetVariable)) {
				target.declareVariable(targetVariable);
			}
		}

		// create a new variable translation for the operation
		VariableTranslation vtRenamed = new VariableTranslation(vtTarget);
		String prefixTarget = "target_";
		String prefixOld = "old_";

		// rename the variables in the state
		vtRenamed.addPrefix(prefixTarget);

		// TODO: add a prefix to the old variables
		// add the variables as additional dimensions
		vtOld.nofVariables();
		long existingDimensions = vtTarget.nofVariables();
		for (Entry<TypedAbstractVariable, Variable> entry : vtOld.getVariables().entrySet()) {
			TypedAbstractVariable normal = entry.getKey();
			TypedAbstractVariable prefixed = new TypedAbstractVariable(prefixOld + normal.getString(),
			        normal.getDeclaration(), normal.getType());
			vtRenamed.getVariables().put(prefixed, new Variable(existingDimensions + entry.getValue().id()));
		}

		// pTarget.add_space_dimensions_and_embed(additionalDimensions);
		// hopefully the dimensions are matching up now
		target.setVariableTranslation(vtRenamed);

		// put the polyhedrons together
		pTarget.concatenate_assign(pOld);

		// apply the expressions
		for (int i = 0; i < targetVariables.size(); i++) {
			TypedAbstractVariable targetVariable = targetVariables.get(i);

			// get the renamed rename target variable
			TypedAbstractVariable renamedVariable = new TypedAbstractVariable(prefixTarget + targetVariable.getString(),
			        targetVariable.getDeclaration(), targetVariable.getType());

			applyExpression(targetState, renamedVariable, arguments.get(i), prefixOld);
		}

		// restore the old variable translation
		target.setVariableTranslation(vtTarget);

		// remove the additional dimensions, this could cause trouble
		pTarget.remove_higher_space_dimensions(existingDimensions);

		target.updateDimensions();
		old.updateDimensions();

		//
		// // remove additional variables
		// for (Entry<TypedAbstractVariable, Variable> entry :
		// vtRenamed.getVariables().entrySet())
		// {
		// if (entry.getKey().getString().startsWith(prefix))
		// {
		// vtRenamed.getVariables().remove(entry.getKey());
		// }
		// }
		// // remove the prefix, undo the renaming
		// vtRenamed.removePrefix(prefix);
	}

	@Override
	public String toString() {
		return s_domainID;
	}

	/**
	 * Returns a string representing the ID of this domain
	 * 
	 * @return
	 */
	public static String getDomainID() {
		return s_domainID;
	}

}
