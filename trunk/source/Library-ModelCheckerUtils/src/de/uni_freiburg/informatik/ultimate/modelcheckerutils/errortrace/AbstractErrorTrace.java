package de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.UUID;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.Boogie2SMTAnnotation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.SMTInterface;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.FormulaArrayBuilder;

public class AbstractErrorTrace extends IErrorTrace{

	/**
	 * 
	 */
	private static final long serialVersionUID = 6467244318295470692L;
	private ErrorTrace mErrorTrace = null;
	private Map<Term, Term> mValuation = null;
	private HashMap<BoogieVar, Term> mInputVariables = null;
	private Logger logger = UltimateServices.getInstance().getLogger("AbstractErrorTrace");
	
	private HashMap<Integer, Integer> mStatementToScopeMap = new HashMap<Integer, Integer>();
	private HashMap<Integer, Term> mScopeToFormulaMap = new HashMap<Integer, Term>();
	
	public AbstractErrorTrace(ErrorTrace errorTrace, HashMap<BoogieVar, Term> inputVariables, Map<Term, Term> valuation) {
		super(errorTrace.getScript());
		mErrorTrace = errorTrace;
		mValuation = valuation;
		mInputVariables = inputVariables;
		this.process();
	}

	protected void process() {
		//TODO use valuation in order to prefix the formulas with an initial state that will make the sequence infeasible
		FormulaArrayBuilder formulaArrayBuilder = new FormulaArrayBuilder(this.getScript());
		ArrayList<IElement> errorPath = buildErrorPath();
		if (errorPath == null)
			throw new NullPointerException("Could not build error path.");
		Term[] formulas = formulaArrayBuilder.getFormulas(errorPath);
		formulas = prefixFormulaWithScope(formulas);
		Term[] interpolants = getInterpolants(formulas);
		if ((interpolants == null) || (interpolants.length + 1 != formulas.length)) {
//			this.addAll(mErrorTrace);
			return;
		}
		ArrayList<ErrorInvariant> relevantErrorInvariants =
				getRelevantErrorInvariants(interpolants, formulas);
		for(int i = 0; i < relevantErrorInvariants.size(); i++) {
			this.add(mErrorTrace.get(relevantErrorInvariants.get(i).getStartOfIntervall()));
		}
	}
	
	private ArrayList<ErrorInvariant> getRelevantErrorInvariants(Term[] interpolants, Term[] formulas) {
		ArrayList<ErrorInvariant> errorInvariants = new ArrayList<ErrorInvariant>();
		HashMap<Term, ErrorInvariant> relevantInterpolants = new HashMap<Term,ErrorInvariant>(); 
		for (int i = 0; i < interpolants.length; i++) {
			if(interpolants[i].equals(this.getScript().term("true"))) {
				continue;
			} else if (relevantInterpolants.keySet().contains(interpolants[i])){
				relevantInterpolants.get(interpolants[i]).setEndOfIntervall(i);
				continue;
			} else {
				ErrorInvariant errorInvariant =
						new ErrorInvariant(interpolants[i], i, formulas);
				errorInvariants.add(errorInvariant);
				relevantInterpolants.put(interpolants[i], errorInvariant);
			}
		}
		return errorInvariants;
	}
	
	private Term[] getInterpolants(Term[] formulas) {
		SMTInterface smtInterface = new SMTInterface(this.getScript());
		Term[] interpolants = null;
		try {
			interpolants = smtInterface.computeInterpolants(formulas);
		} catch (SMTLIBException e) {
			logger.info("Was not able to compress error trace because smt solver returned exception.");
			logger.info(e.getMessage());
		}
		return interpolants;
	}
	
	private ArrayList<IElement> buildErrorPath() {
		ArrayList<Integer> scopeStack = new ArrayList<Integer>();
		Boogie2SMT boogie2SMT = ((Boogie2SMTAnnotation)this.getGraphroot().
				getPayload().getAnnotations().get("Boogie2SMT")).getBoogie2smt();
		ArrayList<IElement> errorPath = new ArrayList<IElement>();
		HashSet<BoogieVar> havocVariables = new HashSet<BoogieVar>(); 
		CFGExplicitNode root = new CFGExplicitNode(this.getScript(), null);
		CFGExplicitNode main = new CFGExplicitNode(this.getScript(), null);
		CFGEdge initEdge = new CFGEdge(this.getScript(), this.getScript().term("true"), root, main);
		errorPath.add(root);
		errorPath.add(initEdge);
		errorPath.add(main);
		for (int i = 0; i < this.getErrorTrace().size(); i++) {
			Statement statement = this.getErrorTrace().get(i);
			Term formula = null;
			Procedure procedure = this.getProcedure();
			if (procedure == null)
				throw new NullPointerException("Could not find procedure declaration.");
			boogie2SMT.declareLocals(procedure);
			boogie2SMT.startBlock();
			boogie2SMT.incGeneration();
			if (statement instanceof AssumeStatement) {
				boogie2SMT.addAssume((AssumeStatement)statement);
				UUID id = UUID.randomUUID();
				Term conditionTerm = 
						VariableSSAManager.makeConstant(id.toString(), this.getScript().sort("Bool"));
				Term condition = this.getScript().term("=", conditionTerm, this.getScript().term("true"));
				mScopeToFormulaMap.put(i, condition);
				formula = this.getScript().term("=>",
						boogie2SMT.getAssumes(), condition);
			} else if (statement instanceof AssertStatement) {
				boogie2SMT.addAssert((AssertStatement)statement);
				formula = boogie2SMT.getAsserts();
			} else if (statement instanceof AssignmentStatement) {
				boogie2SMT.addAssignment((AssignmentStatement)statement);
				formula = boogie2SMT.getAssumes();
			}else if (statement instanceof HavocStatement) {
				boogie2SMT.addHavoc((HavocStatement)statement);
				formula = boogie2SMT.getAssumes();
			} else {
				throw new IllegalArgumentException(statement.toString() +
						" is not supported by abstract error trace.");
			}
			if (formula == null) {
				throw new NullPointerException(
					"Formula of statement \n" + statement + "\n is null.");
			}
			CFGExplicitNode source = (CFGExplicitNode)errorPath.get(errorPath.size()-1);
			HashSet<TermVariable> boogieVars = boogie2SMT.getAllVars();
			HashMap<BoogieVar, TermVariable> boogieInVars = boogie2SMT.getInVars();
			HashMap<BoogieVar, TermVariable> boogieOutVars = boogie2SMT.getOutVars();
			boogie2SMT.endBlock();
			boolean assumptionHasHavocedVariable = false;
			if (statement instanceof HavocStatement) {
				havocVariables.addAll(boogieOutVars.keySet());
			} else if (statement instanceof AssumeStatement) {
				HashSet<BoogieVar> oldHavocVariables = new HashSet<BoogieVar>();
				for (BoogieVar havocVariable: havocVariables) {
					if (boogieOutVars.containsKey(havocVariable)) {
						if (!(boogieOutVars.get(havocVariable).equals(boogieInVars.get(havocVariable)))) {
							oldHavocVariables.add(havocVariable);
						}
					}
				}
				havocVariables.removeAll(oldHavocVariables);
				for (BoogieVar havocVariable: havocVariables) {
					if (boogieInVars.containsKey(havocVariable)) {
						formula = boogie2SMT.getAssumes();
						mScopeToFormulaMap.remove(i);
						assumptionHasHavocedVariable = true;
						break;
					}
				}
			}
			CFGExplicitNode target = new CFGExplicitNode(this.getScript(), null);
			CFGEdge newEdge = new CFGEdge(this.getScript(), formula, source, target);
			errorPath.add(newEdge);
			errorPath.add(target);
			newEdge.getSMTAnnotations().setInVars(boogieInVars);
			newEdge.getSMTAnnotations().setOutVars(boogieOutVars);
			newEdge.getSMTAnnotations().setVars(boogieVars);
			source.getSMTAnnotations().setInVars(boogieInVars);
			source.getSMTAnnotations().setVars(boogieVars);
			scopeStack = updateScopeStack(scopeStack, statement);
			Integer scopeIndex = -1;
			if (!scopeStack.isEmpty()) {
				scopeIndex = scopeStack.get(scopeStack.size()-1);
			}
			if (statement instanceof AssumeStatement) {
				if (!assumptionHasHavocedVariable)
					scopeStack.add(i);
//				scopeIndex = -2;
			}
			mStatementToScopeMap.put(i, scopeIndex);
		}
		return errorPath;
	}
	
	private Term[] prefixFormulaWithScope(Term[] formulas) {
		Term[] result = new Term[formulas.length];
		for(int transitionIndex = 0; transitionIndex < formulas.length; transitionIndex++) {
			Term formula = formulas[transitionIndex];
			Integer scopePrefixIndex = mStatementToScopeMap.get(transitionIndex);
			Term scopedFormula = formula;
			if (scopePrefixIndex != null && scopePrefixIndex > -2) {
//				while (scopePrefixIndex != null && scopePrefixIndex > 0 && scopePrefixIndex < transitionIndex) {
				if (scopePrefixIndex != null && scopePrefixIndex > 0 && scopePrefixIndex < transitionIndex) {
					Term condition = mScopeToFormulaMap.get(scopePrefixIndex);
					if (condition != null) {
					scopedFormula = Util.implies(this.getScript(), 
							condition, scopedFormula);
					}
//					scopePrefixIndex = mStatementToScopeMap.get(scopePrefixIndex);
				}
			}
			result[transitionIndex] = scopedFormula;
		}
		return result;
	}
	
	private void computeMaxIntervals(ArrayList<ErrorInvariant> relevantErrorInvariants, Term[] formulas) {
		
	}
	
	
	private LBool isErrorInvariantFor(ErrorInvariant errorInvariant, Term[] termA, Term[] termB) {
		SMTInterface smtInterface = new SMTInterface(this.getScript());
		Term A = Util.and(this.getScript(), Util.and(this.getScript(), termA),
				Util.not(this.getScript(), errorInvariant.getInvariant()));
		Term B = Util.and(this.getScript(), errorInvariant.getInvariant(),
				Util.and(this.getScript(), termB));
		return smtInterface.checkSatisfiable(Util.and(this.getScript(), A, B));
	}

	private ArrayList<Integer> updateScopeStack(ArrayList<Integer> scopeStack, Statement statement) {
		while (!scopeStack.isEmpty()) {
			int scopesToRemove = isInScope(scopeStack, statement);
			if (scopesToRemove == 0) {
				break;
			}
			for(int i = 0; i < scopesToRemove; i++) {
				scopeStack.remove(scopeStack.size()-1);
			}
		}
		return scopeStack;
	}
	
	private int isInScope(ArrayList<Integer> scopeStack, Statement statement) {
		Integer currentScopeIndex = scopeStack.get(scopeStack.size()-1);
		Statement scope = this.getErrorTrace().get(currentScopeIndex);
		if (scope.equals(statement)) {
			return 1;
		} else if (!isInScopeByLocation(scope.getLocation(), statement.getLocation())) {
			return 1;
		} else if (scope.getLocation().equals(statement.getLocation())) {
			int i = scopeStack.size()-1;
			while (!scopeStack.isEmpty() && i > 0) {
				i--;
				Statement outerScope = this.getErrorTrace().get(scopeStack.get(i));
				ILocation outerScopeLoc = outerScope.getLocation();
				ILocation statementLoc = statement.getLocation();
				if (outerScopeLoc.equals(statementLoc)) {
					if (outerScope.equals(statement)) {
						return scopeStack.size()-i;
					}
				} else {
					break;
				}
			}
		} 
		return 0;
	}
	
	private boolean isInScopeByLocation(ILocation loc1, ILocation loc2) {
		boolean result = false;
		if (loc1.getStartLine() < loc2.getStartLine()) {
			result = true;
		} else if (loc1.getStartLine() == loc2.getStartLine()) {
			if (loc1.getStartColumn() <= loc2.getStartColumn()) {
				result = true;
			}
		}
		if (loc1.getEndLine() > loc2.getEndLine()) {
			result &= true;
		} else if (loc1.getEndLine() == loc2.getEndLine()) {
			if (loc1.getEndColumn() >= loc2.getEndColumn()) {
				result &= true;
			}
		} else {
			result &= false;
		}
		return result;
	}
	
	private ErrorTrace getErrorTrace() {
		return mErrorTrace;
	}
	
	@Override
	public ArrayList<IElement> getErrorPath() {
		return mErrorTrace.getErrorPath();
	}

	@Override
	public Term[] getFormulas() {
		return mErrorTrace.getFormulas();
	}

	@Override
	public IElement getGraphroot() {
		return mErrorTrace.getGraphroot();
	}

	@Override
	public Procedure getProcedure() {
		return mErrorTrace.getProcedure();
	}
}
