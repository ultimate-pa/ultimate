package local.stalin.smt.theory.cclosure;

import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.smt.dpll.Clause;
import local.stalin.smt.dpll.DPLLEngine;
import local.stalin.smt.dpll.Literal;
import local.stalin.smt.dpll.SimpleList;
import local.stalin.smt.dpll.Theory;

public class CClosure implements Theory {
	DPLLEngine engine;
	HashSet<CCTerm> allTerms = new HashSet<CCTerm>();
	//Set<CCTerm.EqualityEntry> allDisEq = new CuckooHashSet<CCTerm.EqualityEntry>();
	CCTermPairHash pairHash = new CCTermPairHash();
	ArrayQueue<Literal> pendingLits = new ArrayQueue<Literal>();
	CCTerm trueTerm;
	HashMap<Object, CCTerm> symbolicTerms =	new HashMap<Object, CCTerm>();
	int numFunctionPositions;
	
	public CClosure(DPLLEngine engine) {
		this.engine = engine;
	}
	
	private CCTerm getTrueTerm() {
		if (trueTerm == null)
			trueTerm = new CCBaseTerm(false, numFunctionPositions, Atom.TRUE);
		return trueTerm;
	}
	
	public CCTerm createAnonTerm(Term name) {
		CCTerm term = new CCBaseTerm(false, numFunctionPositions, name);
		allTerms.add(term);
		return term;
	}

	private CCTerm createAppTerm(boolean isFunc, CCTerm func, CCTerm arg) {
		assert(func.isFunc);
		SimpleList<CCAppTerm.Parent> prevParents =  arg.ccpars.getParentInfo(func.parentPosition);
		assert(prevParents.wellformed());
		for (CCAppTerm.Parent termpar : prevParents) {
			CCAppTerm term = termpar.getData();
			if (term.func == func)
				return term;
		}
		CCAppTerm term = new CCAppTerm(isFunc, 
				isFunc ? func.parentPosition + 1 : numFunctionPositions, func, arg);
		return term;
	}
	
	private CCTerm convertPredTerm(PredicateSymbol sym, CCTerm[] args, int numArgs) {
		if (numArgs == 0) {
			CCTerm term = symbolicTerms.get(sym);
			if (term == null) {
				term = new CCBaseTerm(args.length > 0, numFunctionPositions, sym);
				numFunctionPositions += args.length;
				symbolicTerms.put(sym, term);
			}
			return term;
		} else {
			CCTerm pred = convertPredTerm(sym, args, numArgs-1);
			return createAppTerm(numArgs < args.length, pred, args[numArgs-1]);
		}
	}
	
	private CCTerm convertFuncTerm(FunctionSymbol sym, CCTerm[] args, int numArgs) {
		if (numArgs == 0) {
			CCTerm term = symbolicTerms.get(sym);
			if (term == null) {
				term = new CCBaseTerm(args.length > 0, numFunctionPositions, sym);
				numFunctionPositions += args.length;
				symbolicTerms.put(sym, term);
			}
			return term;
		} else {
			CCTerm pred = convertFuncTerm(sym, args, numArgs-1);
			return createAppTerm(numArgs < args.length, pred, args[numArgs-1]);
		}
	}
	
	public EqualityAtom createEquality(CCTerm t1, CCTerm t2) {
		return createEquality(t1, t2, null);
	}
	public EqualityAtom createEquality(CCTerm t1, CCTerm t2, TermVariable mixedVar) {
		assert (t1 != t2);
		CCTermPairHash.Info info = pairHash.getInfo(t1.rep, t2.rep);
		if (info == null) {
			info = new CCTermPairHash.Info(t1.rep, t2.rep);
			pairHash.add(info);
		}
		for (CCTermPairHash.EqualityEntry eql : info.eqlits) {
			EqualityAtom l = eql.getData();
			if (l.getLhs() == t1 && l.getRhs() == t2)
				return l;
			if (l.getRhs() == t1 && l.getLhs() == t2)
				return l;
		}
		EqualityAtom l = new EqualityAtom(this, t1, t2, mixedVar);
		engine.addAtom(l);
		info.eqlits.append(new CCTermPairHash.EqualityEntry(l));
		return l;
	}
	public Literal createPredAtom(PredicateSymbol sym, CCTerm[] subterms, int formNumber) {
		CCTerm pred = convertPredTerm(sym, subterms, subterms.length);
		CCTerm trueTerm = getTrueTerm();
		pred.occursIn(formNumber);
		trueTerm.occursIn(formNumber);
		return createEquality(pred, trueTerm);
	}
	public CCTerm createFuncTerm(FunctionSymbol sym, CCTerm[] subterms) {
		CCTerm term = convertFuncTerm(sym, subterms, subterms.length);
		allTerms.add(term);
		return term;
	}
	public CCTerm createTermVariableTerm(TermVariable tv) {
		CCTerm term = symbolicTerms.get(tv);
		if (term == null) {
			term = new CCBaseTerm(false, numFunctionPositions, tv);
			symbolicTerms.put(tv, term);
			// TODO: Remove this once we are clear about errors in Groundifier
			allTerms.add(term);
		}
		return term;
	}
			
	//@Override
	public void backtrackLiteral(Literal literal) {
		if (pendingLits.size() > 0)
			pendingLits.clear();
		if (literal instanceof EqualityAtom) {
			EqualityAtom atom = (EqualityAtom) literal;
			CCTerm lhs = atom.getLhs();
			CCTerm rhs = atom.getRhs();
			if (lhs.equalEdge == rhs) {
				if (lhs.oldRep.reasonLiteral != null)
					lhs.undoMerge(this, rhs);
			} else if (rhs.equalEdge == lhs) {
				if (rhs.oldRep.reasonLiteral != null)
					rhs.undoMerge(this, lhs);
			}
		} else if (literal.negate() instanceof EqualityAtom){
			undoSep((EqualityAtom) literal.negate());
		}
	}

	//@Override
	public Clause computeConflictClause() {
		return null;
	}

	//@Override
	public Clause getConflictClause() {
		return null;
	}

	public Literal getPropagatedLiteral() {
		Literal lit = pendingLits.poll();
		if (lit != null && lit.negate() instanceof EqualityAtom) {
			EqualityAtom atom = (EqualityAtom) lit.negate();
			assert pairHash.getInfo(atom.getLhs().rep, atom.getRhs().rep).diseq != null 
			    &&  pairHash.getInfo(atom.getLhs().rep, atom.getRhs().rep).diseq != atom;
		}
		return lit;
	}
	
	//@Override
	public Clause getUnitClause(Literal lit) {
		if (lit instanceof EqualityAtom) {
			return computeCycle((EqualityAtom) lit);
		} else {
			/* ComputeAntiCycle */
			return computeAntiCycle((EqualityAtom) lit.getAtom());
		}
	}

	//@Override
	public Clause setLiteral(Literal literal) {
		if (literal instanceof EqualityAtom) {
			EqualityAtom atom = (EqualityAtom) literal;
			if (atom.getLhs().rep != atom.getRhs().rep)
				return atom.getLhs().merge(this, atom.getRhs(), atom);
		} else if (literal.negate() instanceof EqualityAtom) {
			EqualityAtom atom = (EqualityAtom) literal.negate();
			CCTerm left = atom.getLhs().rep;
			CCTerm right = atom.getRhs().rep;

			/* Check for conflict */
			if (left == right)
				return computeCycle(atom);
			separate(left, right, atom);
		}
		return null;
	}

	private CCTermPairHash.Info lastInfo;
	private void separate(CCTerm lhs, CCTerm rhs, EqualityAtom atom) {
		if (lastInfo == null || !lastInfo.equals(lhs, rhs)) {
			lastInfo = pairHash.getInfo(lhs, rhs);
			assert lastInfo != null;
		}
		if (lastInfo.diseq != null)
			return;

		lastInfo.diseq = atom;
		/* Propagate inequalities */
		for (CCTermPairHash.EqualityEntry eql : lastInfo.eqlits) {
			EqualityAtom eq = eql.getData();
			if (eq.getDecideStatus() == null) {
				addPending(eq.negate());
			}
		}
		/* reverse congruence closure
		for (CCTerm t1 : members) {
			if (t1 instanceof CCAppTerm) {
				CCAppTerm app1 = (CCAppTerm) t1;
				for (CCTerm t2 : members) {
					if (t2 instanceof CCAppTerm) {
						CCAppTerm app2 = (CCAppTerm) t2;
						if (app1.func.rep == app2.func.rep
							&& !app1.arg.rep.inDiseq(app2.arg.rep.diseq)) {
							separate(app1.arg.rep, app2.arg.rep, atom);
						} else if (app1.arg.rep == app2.arg.rep
								   && !app1.func.rep.inDiseq(app2.func.rep.diseq)) {
							separate(app1.func.rep, app2.func.rep, atom);
						}
					}
				}
			}
		} */
	}
	
	private void undoSep(EqualityAtom atom) {
		CCTermPairHash.Info destInfo = pairHash.getInfo(atom.getLhs().rep, atom.getRhs().rep);
		assert destInfo != null;
		if (destInfo.diseq == atom)
			destInfo.diseq = null;
	}	

	public Clause computeCycle(EqualityAtom eq) {
		CongruencePath congPath = 
			new CongruencePath(this, engine.getFormulaCount()-1);
		return congPath.computeCycle(eq);
	}
		
	public Clause computeAntiCycle(EqualityAtom eq) {
		CCTerm left = eq.getLhs();
		CCTerm right = eq.getRhs();
		
		CCTermPairHash.Info destInfo = pairHash.getInfo(left.rep, right.rep);
		EqualityAtom diseq = destInfo.diseq;
		assert left.rep != right.rep;
		
		ArrayQueue<Literal> pending = pendingLits;
		pendingLits = new ArrayQueue<Literal>();
		Clause c = left.merge(this, right, eq);
		if (c == null)
			c = computeCycle(diseq);
		/* Unmerge, in case the merge partially succeeded */
		if (left.equalEdge == right)
			left.undoMerge(this, right);
		else if (right.equalEdge == left)
			right.undoMerge(this, left);
		pendingLits = pending;
		return c;
	}
	
	public void addPending(Literal eq) {
		if (eq.negate() instanceof EqualityAtom) {
			EqualityAtom atom = (EqualityAtom) eq.negate();
			assert pairHash.getInfo(atom.getLhs().rep, atom.getRhs().rep).diseq != null 
			    &&  pairHash.getInfo(atom.getLhs().rep, atom.getRhs().rep).diseq != atom;
		}
		pendingLits.add(eq);
	}


	public Clause checkpoint() {
		// TODO Move some functionality from setLiteral here.
		return null;
	}
	
	public Atom convertPredToSMT(CCTerm t) {
		CCTerm pred = t;
		while (pred instanceof CCAppTerm)
			pred = ((CCAppTerm) pred).func;
		PredicateSymbol sym = (PredicateSymbol) ((CCBaseTerm) pred).symbol;
		Term[] args = new Term[sym.getParameterCount()];
		int dest = args.length;
		while (t instanceof CCAppTerm) {
			args[--dest] = convertTermToSMT(((CCAppTerm)t).arg);
			t = ((CCAppTerm) t).func;
		}
		return engine.getSMTTheory().atom(sym, args);
	}
	
	public Term convertTermToSMT(CCTerm t) {
		if (t instanceof CCBaseTerm &&
			((CCBaseTerm) t).symbol instanceof Term)
			return (Term) ((CCBaseTerm) t).symbol;
		CCTerm func = t;
		while (func instanceof CCAppTerm)
			func = ((CCAppTerm) func).func;
		// HACK for TermVariables...
		// TODO: @Jochen: Is there a better way to do this???
		CCBaseTerm basefunc = (CCBaseTerm)func;
		if (basefunc.symbol instanceof TermVariable)
			return engine.getSMTTheory().term((TermVariable)basefunc.symbol);
		FunctionSymbol sym = (FunctionSymbol) ((CCBaseTerm) func).symbol;
		Term[] args = new Term[sym.getParameterCount()];
		int dest = args.length;
		while (t instanceof CCAppTerm) {
			args[--dest] = convertTermToSMT(((CCAppTerm)t).arg);
			t = ((CCAppTerm) t).func;
		}
		return engine.getSMTTheory().term(sym, args);
	}

	public Formula convertEqualityToSMT(CCTerm t1, CCTerm t2) {
		if (t1 == trueTerm)
			return convertPredToSMT(t2);
		if (t2 == trueTerm)
			return convertPredToSMT(t1);
		return engine.getSMTTheory().equals(convertTermToSMT(t1), 
				convertTermToSMT(t2));
	}
	

	public void dumpModel(Logger logger) {
		logger.info("Equivalence Classes:");
		for (CCTerm t : allTerms) {
			if (t == t.rep) {
				StringBuilder sb = new StringBuilder();
				String comma = "";
				for (CCTerm t2 : t.members) {
					sb.append(comma).append(t2);
					comma = "=";
				}
				logger.info(sb.toString());
			}
		}
		if (trueTerm != null) {
			StringBuilder sb = new StringBuilder("True Predicates: ");
			String comma = "";
			for (CCTerm t : trueTerm.rep.members) {
				if (t != trueTerm) {
					sb.append(comma).append(t);
					comma = ", ";
				}
			}
			logger.info(sb.toString());
		}
	}

	public void printStatistics(Logger logger) {
		logger.info("CCTimes: iE "+CCTerm.invertEdgeTime+" eq "+CCTerm.eqTime +
				" cc "+CCTerm.ccTime + " setRep "+CCTerm.setRepTime);
		logger.info("Merges: "+CCTerm.mergeCount+ ", cc:"+CCTerm.ccCount);
	}
}
