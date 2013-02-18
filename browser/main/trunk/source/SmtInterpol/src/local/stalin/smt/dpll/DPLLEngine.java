package local.stalin.smt.dpll;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.FormulaWalker;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.ITETerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.VariableTerm;
import local.stalin.logic.FormulaWalker.SymbolVisitor;
import local.stalin.smt.dpll.Clause.Watcher;
import local.stalin.smt.hack.SymbolRange;
import local.stalin.smt.theory.cclosure.CuckooHashSet;

import org.apache.log4j.Logger;

/**
 * The DPLL engine.
 * @author hoenicke
 *
 */
public class DPLLEngine {
	private static class VarDetector implements SymbolVisitor {

		private HashSet<TermVariable> m_Vars = new HashSet<TermVariable>();
		
		@Override
		public void done(Term input) {}

		@Override
		public void done(PredicateAtom pa) {}

		@Override
		public void endscope(TermVariable tv) {
			m_Vars.remove(tv);
		}

		@Override
		public void endscopes(TermVariable[] tvs) {
			for (TermVariable t : tvs)
				m_Vars.remove(t);
		}

		@Override
		public void let(TermVariable tv, Term mval) {}

		@Override
		public Formula predicate(PredicateAtom pa) {
			return null;
		}

		@Override
		public void quantifier(TermVariable[] tvs) {}

		@Override
		public Term term(Term input) {
			if (input instanceof VariableTerm)
				m_Vars.add(((VariableTerm)input).getVariable());
			else if ((input instanceof ApplicationTerm) || 
					(input instanceof ITETerm))
				return null;
			return input;
		}

		@Override
		public boolean unflet() {
			return false;
		}

		@Override
		public boolean unlet() {
			return false;
		}
		public boolean contains(TermVariable tv) {
			return m_Vars.contains(tv);
		}
		public void clear() {
			m_Vars.clear();
		}
	}
	private Logger logger;

	/* Statistics */
	private int conflicts, decides, tprops, props;
	private int num_solvedatoms, num_clauses, num_axiomclauses;
	private SimpleList<Clause> learnedClauses = new SimpleList<Clause>();
	private long propTime, explainTime, setTime, backtrackTime;
	private static final boolean profileTime = false;
	private static final boolean printStatistics = true;
	private local.stalin.logic.Theory smtTheory;
	private VarDetector vardetect;
	private FormulaWalker vardetectwalker;
	
	private static final double LIMIT = 1e250;
	private static final double CLAUSE_UNLEARN_ACTIVITY = 1e-150;
	
	/**
	 * The number of formulas of which we should compute interpolants.
	 */
	int numFormulas = 0;
	
	double atom_scale = 1 - 1.0/ATOM_ACTIVITY_FACTOR;
	double cls_scale = 1 - 1.0/CLS_ACTIVITY_FACTOR;
	private static final double ATOM_ACTIVITY_FACTOR = 1.1;
	private static final double CLS_ACTIVITY_FACTOR = 1.01;

	private static final boolean DEEP_BACKTRACK = true;

	private static final int RESTART_FACTOR = 500;
	
	/**
	 * The list of unit clauses that are not yet decided.
	 */
	SimpleList<Watcher> changedList = new SimpleList<Watcher>();
	
	ArrayList<Literal> decideStack = new ArrayList<Literal>();
	
	/**
	 * The list of all theories.
	 */
	private Theory[] theories = new Theory[0];
	private TreeSet<DPLLAtom> atoms = new TreeSet<DPLLAtom>();

	private int currentDecideLevel = 0;
	InterpolationInfo trueIp = new InterpolationInfo(Atom.TRUE);

	private Formula[] interpolants;

	/**
	 * Contains mapping to <code>Boolean.TRUE</code> iff TermVariable should 
	 * be existentially quantified. Mapping to <code>Boolean.FALSE</code> iff
	 * it should be universally quantified.
	 */
	private Map<TermVariable,SymbolRange> instantiationMap;
	
	/**
	 * Ordering relation for quantifier inference. If a mapping exists for a
	 * variable v, we first have to infer quantifiers for all elements in the
	 * dependency set.
	 */
	private Map<TermVariable,Set<TermVariable>> inferOrder;
	
	public void setInstantiationMap(Map<TermVariable,SymbolRange> theInstMap) {
		instantiationMap = theInstMap;
	}
	
	public void setInferenceOrder(Map<TermVariable,Set<TermVariable>> inford) {
		inferOrder = inford;
	}
	
	public DPLLEngine(local.stalin.logic.Theory smtTheory,Logger logger) {
		this.smtTheory = smtTheory;
		vardetect = new VarDetector();
		vardetectwalker = new FormulaWalker(vardetect,smtTheory);
		this.logger = logger == null ? Logger.getRootLogger() : logger;
	}
	
	public int getDecideLevel() {
		return currentDecideLevel;
	}
	
	public void insertPropagatedLiteral(Theory t, Literal lit, int decideLevel) {
		int stackptr = decideStack.size();
		int level = currentDecideLevel;
		while (level > decideLevel) {
			if (decideStack.get(--stackptr).getAtom().explanation == null)
				level--;
		}
		decideStack.add(stackptr, lit);
		if (decideLevel == 0) {
			/* This atom is now decided once and for all. */
			num_solvedatoms++;
		}
		DPLLAtom atom = lit.getAtom();
		assert !atoms.contains(atom);
		atom.explanation = t;
		atom.decideLevel = decideLevel;
		atom.decideStatus = lit;
		atom.lastStatus = atom.decideStatus;
		assert checkDecideLevel();
	}
	
	/**
	 * Propagate unit clauses first in boolean part, then in 
	 * the theory part.
	 * @return a conflict clause if a conflict was detected.
	 */
	public Clause propagate() {
		
		while (true) {
			Clause conflict = propagateTheories();
			if (conflict != null)
				return conflict;
			
			int level = decideStack.size();
			conflict = propagateClauses();
			if (conflict != null)
				return conflict;
			if (decideStack.size() > level)
				continue;
			
			level = decideStack.size();
			for (Theory t: theories) {
				conflict = t.checkpoint();
				if (conflict != null)
					return conflict;
			}

			conflict = propagateTheories();
			if (conflict != null)
				return conflict;
			if (decideStack.size() == level)
				return null;
		}
	}
	
	private Clause propagateTheories() {
		while (true) {
			boolean changed = false;
			for (Theory t: theories) {
				Literal propLit = t.getPropagatedLiteral();
				if (propLit != null) {
					do {
						if (propLit.atom.decideStatus == null) {
							tprops++;
							propLit.atom.explanation = t;
							Clause conflict = setLiteral(propLit);
							if (conflict != null) {
								for (Literal lit: conflict.literals) {
									DPLLAtom atom = lit.getAtom();
									assert(atom.decideStatus == lit.negate());
								}
								assert(conflict.interpolants != null);
								return conflict;
							}
						} else if (propLit.atom.decideStatus != propLit)
							return t.getUnitClause(propLit);
						propLit = t.getPropagatedLiteral();
					} while (propLit != null);
					changed = true;
				}
			}
			if (!changed)
				return null;
		}
	}
		
	private Clause propagateClauses() {
	nextList:
		while (!changedList.isEmpty()) {
			Watcher entry = changedList.removeFirst();
			Clause clause = entry.getElem().getClause();
			Literal[] lits = clause.literals;
			/* Special case bottom clause: just return it as conflict clause */
			if (lits.length == 0)
				return clause;
			int index = clause.firstWatch == entry ? 0 : 1;
			Literal otherLit = 
				lits[lits.length == 1 ? 0 : 1-index];
			DPLLAtom otherAtom = otherLit.getAtom(); 
			if (otherAtom.decideStatus == otherLit) {
				/* Other watcher is true, put ourself on
				 * backtrack watcher list.
				 */
				otherAtom.backtrackWatchers.append(entry);
				continue nextList;
			}
			if (lits.length > 1) {
				Literal myLit = lits[index];
				if (myLit.getAtom().decideStatus != 
					myLit.negate()) {
					myLit.watchers.append(entry);
					continue nextList;
				}
				for (int i = 2; i < lits.length; i++) {
					Literal lit = lits[i];
						DPLLAtom atom = lit.getAtom();
					Literal status = atom.decideStatus;
					if (status != lit.negate()) {
						/* check if clause is too old to keep */
						if (clause.activity < cls_scale * CLAUSE_UNLEARN_ACTIVITY
								&& status == null) {
							Watcher w = clause.firstWatch;
							if (w == entry)
								w = clause.secondWatch;
							w.removeFromList();
							clause.removeFromList();
						} else {
							/* watch this literal */
							lits[index] = lit;
							lits[i] = myLit;
							lit.watchers.append(entry);
						}
						continue nextList;
					}
				}
			}
			/* Now we haven't found another atom to watch.  Hence we have
			 * a unit clause or conflict clause.
			 */
			if (otherAtom.decideStatus == null) {
				/* Propagate the unit clause. */
				otherAtom.explanation = clause;
				otherAtom.backtrackWatchers.append(entry);
				props++;
				return setLiteral(otherLit);
			}
			/* Conflict clause */
			// put the entry back in changedList, we will need to
			// backtrack first.
			changedList.append(entry);
			return clause;
		}
		return null;
	}
	
	/**
	 * Sets a literal to true and tells all theories about it.  The
	 * literal must be undecided when this function is called.
	 * @param literal the literal to set.
	 * @return a conflict clause if a conflict was detected.
	 */
	private Clause setLiteral(Literal literal) {
		if (logger.isDebugEnabled())
			logger.debug(decideStack.size()+": Setting Literal "+literal+ "("+literal.getAtom().explanation+")");
		DPLLAtom atom = literal.getAtom();
		assert (atom.decideStatus == null);
		assert atoms.contains(atom);
		if (currentDecideLevel == 0) {
			/* This atom is now decided once and for all. */
			// TODO: Should we remove it from literals?
			num_solvedatoms++;
		}
		decideStack.add(literal);
		atom.decideLevel = currentDecideLevel;
		atom.decideStatus = literal;
		atom.lastStatus = atom.decideStatus;
		atoms.remove(atom);
		assert checkDecideLevel();
		changedList.moveAll(literal.negate().watchers);
		long time;
		if (profileTime)
			time = System.nanoTime();
		Clause conflict = null;
		for (Theory t: theories) {
			conflict = t.setLiteral(literal); 
			if (conflict != null) {
				assert(conflict.interpolants != null);
				for (Literal lit: conflict.literals) {
					DPLLAtom a = lit.getAtom();
					assert(a.decideStatus == lit.negate());
				}
				break;
			}
		}
		if (profileTime)
			setTime += System.nanoTime() - time;
		return conflict;
	}

	public void learn(Clause clause) {
		clause.createWatchers();
		/* A clause is "learned" if it appears on either the
		 * changedList or the watchers list of some atom.
		 */
		changedList.append(clause.firstWatch);
		changedList.append(clause.secondWatch);
	}

	public void addClause(Clause clause) {
		atom_scale += 1.0-(1.0/1.1);
		learn(clause);
		clause.activity = Double.POSITIVE_INFINITY;
		num_axiomclauses++;
	}

	public void addFormulaClause(Literal[] literals, int formula) {
		atom_scale += 1.0-(1.0/ATOM_ACTIVITY_FACTOR);
		Clause clause = new Clause(literals, formula);
		learn(clause);
		clause.activity = Double.POSITIVE_INFINITY;
		num_axiomclauses++;
	}
	
	public Formula orFormula(Formula f1, Formula f2) {
		if (f1 == Atom.TRUE || f2 == Atom.FALSE || f1 == f2)
			return f1;
		if (f2 == Atom.TRUE || f1 == Atom.FALSE)
			return f2;
		return smtTheory.or(f1, f2);
	}
	
	public Formula andFormula(Formula f1, Formula f2) {
		if (f2 == Atom.TRUE || f1 == Atom.FALSE || f1 == f2)
			return f1;
		if (f1 == Atom.TRUE || f2 == Atom.FALSE)
			return f2;
		return smtTheory.and(f1, f2);
	}
	
	public Formula implFormula(Formula f1, Formula f2) {
		if (f1 == Atom.FALSE || f1 == f2)
			return Atom.TRUE;
		if (f2 == Atom.FALSE)
			return smtTheory.not(f1);
		if (f1 == Atom.TRUE || f2 == Atom.TRUE)
			return f2;
		return smtTheory.implies(f1, f2);
	}
	
	public void computeInterpolants() {
		for (Watcher w : changedList) {
			Clause c = w.getClause();
			if (c.interpolants != null)
				continue;
			InterpolationInfo[] interpolants = new InterpolationInfo[numFormulas-1];
			for (int i = 0; i < c.formulaNr; i++)
				interpolants[i] = trueIp;
			for (int i = c.formulaNr; i < numFormulas-1; i++) {
				Formula f = Atom.FALSE;
				for (Literal l : c.literals) {
					if (l.getAtom().getLastFormulaNr() > i)
						f =	orFormula(l.getSMTFormula(smtTheory), f);
				}
				interpolants[i] = new InterpolationInfo(f);
			}
			c.interpolants = interpolants;
		}
	}
	
	private boolean checkDecideLevel() {
		int decision = 0;
		for (Literal lit : decideStack) {
			if (lit.getAtom().explanation == null)
				decision++;
			assert lit.getAtom().decideLevel == decision;
		}
		return decision == currentDecideLevel;
	}
	
	/*
	private static final int TOANALYZE = 1;
	private static final int REDUNDANT = 2;
	private void removeRedundancy(Set<Literal> clause) {
		for (Literal l: clause)
			l.getAtom().dpllFlags = TOANALYZE;
		int stackPtr = decideStack.size();
		while (stackPtr > 0) {
			Literal lit = decideStack.get(--stackPtr);
			if (lit.getAtom().dpllFlags == TOANALYZE) {
				Object explanation = lit.getAtom().explanation;
				if (explanation == null)
					continue;
				if (!(explanation instanceof Clause)) {
					explanation = ((Theory) explanation).getUnitClause(lit);
					lit.getAtom().explanation = explanation;
				}
				Clause expl = (Clause) explanation;
				for (Literal l2 : expl.literals) {
					if (l2.getAtom().decideLevel > 0)
						l2.getAtom().dpllFlags = TOANALYZE;
				}
			}
		}
		stackptr:
		while (stackPtr < decideStack.size()) {
			Literal l = decideStack.get(stackPtr++);
			if (l.getAtom().dpllFlags == TOANALYZE) {
				Clause expl = (Clause) l.getAtom().explanation;
				if (expl != null) {
					for (Literal l2 : expl.literals) {
						if (l2.getAtom().decideLevel > 0
							&& l2.getAtom().dpllFlags != REDUNDANT
							&& !clause.contains(l2)) {
							l.getAtom().dpllFlags = 0;
							continue stackptr;
						}
					}
					l.getAtom().dpllFlags = REDUNDANT;
				}
			}
		}
		Iterator<Literal> it = clause.iterator();
		while (it.hasNext())
			if (it.next().getAtom().dpllFlags == REDUNDANT)
				it.remove();
	}
	*/
	
	/**
	 * Check if there no other conflict literal between the
	 * current point and the last decided literal.  In that case
	 * we can backtrack all literals until the backtracking point
	 * and stop explaining the conflict.
	 */
	private boolean isBacktrackingPoint(Set<Literal> conflict) {
		if (currentDecideLevel == 0)
			return false;
		int stackPtr = decideStack.size();
		while (true) {
			Literal olit = decideStack.get(--stackPtr);
			if (conflict.contains(olit))
				return false;
			if (olit.getAtom().explanation == null)
				return true;
		}
	}
	
	private Clause explainConflict(Clause clause) {
		logger.debug("Clause " + clause + " has support " + clause.tvsupport);
		Set<TermVariable> pendingSet;
		if (clause.pendingSet != null)
			pendingSet = new HashSet<TermVariable>(clause.pendingSet);
		else
			pendingSet = new HashSet<TermVariable>();
		conflicts++;
		assert checkDecideLevel();
		if (logger.isDebugEnabled())
			logger.debug("explaining clause "+clause+ " with ip: "+Arrays.toString(clause.interpolants));
		if (clause.literals.length == 0) {
			/* Conflict is already Bottom */
			return clause;
		}
		/* Don't use clone, since the array must be of type InterpolationInfo[] */
		InterpolationInfo[] newInterpolants = new InterpolationInfo[clause.interpolants.length];
		System.arraycopy(clause.interpolants, 0, newInterpolants, 0, clause.interpolants.length);
		atom_scale *= ATOM_ACTIVITY_FACTOR;
		cls_scale *= CLS_ACTIVITY_FACTOR;
		Set<Literal> conflict = new CuckooHashSet<Literal>();
		for (Literal lit: clause.literals) {
			DPLLAtom atom = lit.getAtom();
			assert(atom.decideStatus == lit.negate());
			/* This optimization breaks interpolation, so remove it for now */
			//if (atom.decideLevel > 0)
				conflict.add(lit.negate());
			atom.activity += atom_scale;
		}
		if (conflict.size() == 0) {
			/* Unsatisfiable
			 */
			return new Clause(new Literal[0], newInterpolants);
		}
		Map<TermVariable,Integer> quantifierInference = new HashMap<TermVariable,Integer>(clause.tvsupport);
		while (true) {
			Literal lit = decideStack.remove(decideStack.size()-1);
			Object explanation = lit.getAtom().explanation;
			assert(!conflict.contains(lit.negate()));
			if (!conflict.contains(lit)) {
				if (explanation == null)
					currentDecideLevel--;
				assert checkDecideLevel();
				backtrackLiteral(lit);
			} else if (explanation == null 
				|| isBacktrackingPoint(conflict)) {
				/* This literal need not be explained; we resolve
				 * the conflict if we just backtrack until the last 
				 * decision point.
				 */
				while (lit.getAtom().explanation != null) {
					backtrackLiteral(lit);
					lit = decideStack.remove(decideStack.size()-1);
				}
				backtrackLiteral(lit);
				currentDecideLevel--;
				assert checkDecideLevel();
				
				/* We removed at least one decision point.
				 * Try to backtrack further.
				 */
				if (DEEP_BACKTRACK)
					findBacktrackingPoint(conflict);
				
				if (logger.isDebugEnabled())
					logger.debug(decideStack.size()+": Backtracking point");
				//removeRedundancy(conflict);
				Literal[] newlits = new Literal[conflict.size()];
				int i = 0;
				for (Literal l : conflict) {
					newlits[i++] = l.negate();
				}
				assert newlits[newlits.length-1] != null;
				Clause resolution = new Clause(newlits, newInterpolants);
				if (!pendingSet.isEmpty())
					resolution.pendingSet = pendingSet;
				resolution.activity = cls_scale;
				if (conflict.size() <= 2)
					resolution.activity = Double.POSITIVE_INFINITY;
				assert(resolution.interpolants != null);
				learn(resolution);
				learnedClauses.append(resolution);
				num_clauses++;
				if (logger.isDebugEnabled())
					logger.debug("Resolved to " + resolution + " with interpolants " + Arrays.toString(resolution.interpolants));
				return resolution;
			} else {
				Clause expl = null;
				/* Do a resolution step with explanation */
				if (explanation instanceof Theory) {
					expl = ((Theory) explanation).getUnitClause(lit);
				} else {
					expl = (Clause) explanation;
				}
				if (expl.pendingSet != null)
					pendingSet.addAll(expl.pendingSet);
				backtrackLiteral(lit);
				conflict.remove(lit);
				logger.debug("expl " + expl + " has support " + expl.tvsupport);
				expl.activity += cls_scale;
				expl.usedTimes++;
				// update inference map.
				for (Map.Entry<TermVariable,Integer> me : expl.tvsupport.entrySet() ) {
					Integer oldval = quantifierInference.get(me.getKey());
					if (oldval == null)
						quantifierInference.put(me.getKey(),me.getValue());
					else
						quantifierInference.put(me.getKey(),oldval + me.getValue());
				}
				if (lit.getAtom().instantiationVars != null) {
					for (TermVariable tv : lit.getAtom().instantiationVars) {
						Integer old = quantifierInference.get(tv);
						assert(old != null);
						// We need to subtract two since we now have lit and lit.negate() contributing to the support...
						int newval = old - 2;
						if (newval == 0) {
							quantifierInference.remove(tv);
							pendingSet.add(tv);
						} else
							quantifierInference.put(tv,newval);
					}
				}
				DPLLAtom atom = lit.getAtom();
				if (logger.isDebugEnabled())
					logger.debug("Resolving with " + expl + " with interpolants " + Arrays.toString(expl.interpolants) + " pivot = " + atom);
				assert(expl.interpolants != null);
				for (Literal l : expl.literals) {
					if (l != lit) {
						assert(l != lit.negate());
						assert(l.getAtom().decideStatus == l.negate());
						/* This optimization breaks interpolation, so remove it for now */
						//if (l.getAtom().decideLevel > 0)
							if (!conflict.add(l.negate())) {
								// Literal already contained in conflict => Adjust quantifier inference counters
								Set<TermVariable> ltvsupport = l.getAtom().instantiationVars;
								if (ltvsupport != null) {
									for (TermVariable tv : ltvsupport) {
										Integer old = quantifierInference.get(tv);
										assert(old != null);
										int newval = old - 1;
										if (newval == 0) {
											quantifierInference.remove(tv);
											pendingSet.add(tv);
										} else
											quantifierInference.put(tv,newval);
									}
								}
							}
						l.getAtom().activity += atom_scale;
					}
				}
				//logger.info("Explained by: "+conflict);
				for (int i = 0; i < numFormulas - 1; i++) {
					assert newInterpolants[i].getFormula() != null;
					assert expl.interpolants[i].getFormula() != null;
					//logger.info("adding clause "+expl+ " with ip: "+Arrays.toString(expl.interpolants));
					newInterpolants[i] = 
						newInterpolants[i].interpolate(this, atom, i, expl.interpolants[i]);
					assert newInterpolants[i].interpolant != null;
				}
				// Quantifier inference loop
				LinkedList<TermVariable> inference =
					new LinkedList<TermVariable>(pendingSet);
				pendingSet = new HashSet<TermVariable>();
				TermVariable var;
				/* Termination is hard to see: Actually, this is a
				 * topological sort on the dependency DAG.
				 */
				infer: while ((var = inference.pollFirst()) != null) {
					Set<TermVariable> deps = inferOrder.get(var);
					if (deps != null) {
						for (TermVariable dep : deps) {
							if (inference.contains(dep)) {
								// First handle dependency, then this variable
								inference.offerLast(var);
								continue infer;
							}
							if (quantifierInference.containsKey(dep) || 
									pendingSet.contains(dep)) {
								// Wait until dependencies are resolved
								pendingSet.add(var);
								continue infer;
							}
								
						}
					}
					// Either no deps or deps satisfied.
					SymbolRange quant = instantiationMap.get(var);
					for (int i = 0; i < numFormulas - 1; ++i) {
						Formula ip = newInterpolants[i].getFormula();
						vardetect.clear();
						vardetectwalker.process(ip);
						if (vardetect.contains(var)) {
							if (i < quant.first)
								// B-local
								newInterpolants[i] = 
									new InterpolationInfo(
										smtTheory.forall(new TermVariable[] {var}, ip),
											newInterpolants[i].mixedLiteralInterpolator);
							else if (i >= quant.last)
								// A-local
								newInterpolants[i] =
									new InterpolationInfo(
											smtTheory.exists(new TermVariable[] {var}, ip),
												newInterpolants[i].mixedLiteralInterpolator);
							else
								throw new AssertionError("Unneeded purification variable!");
						}
					}
				}
				if (logger.isDebugEnabled()) {
					logger.debug("new conflict: "+conflict);
					logger.debug("new interpolants: "+Arrays.toString(newInterpolants));
					logger.debug("Quantifier Inference Counters: " + quantifierInference);
				}
				if (conflict.size() == 0) {
					/* Unsatisfiable */
					return new Clause(new Literal[0], newInterpolants);
				}
			}
		}
	}

	private void findBacktrackingPoint(Set<Literal> conflict) {
		int i = decideStack.size();
		while (i > 0) {
			Literal lit = decideStack.get(--i);
			if (conflict.contains(lit))
				break;
			if (lit.getAtom().explanation == null) {
				while (decideStack.size() > i)
					backtrackLiteral(decideStack.remove(decideStack.size()-1));
				currentDecideLevel--;
			}
		}
	}

	private void backtrackLiteral(Literal literal) {
		long time;
		if (profileTime)
			time = System.nanoTime();
		//logger.info("Backtrack: "+literal);
		DPLLAtom atom = literal.getAtom();
		changedList.moveAll(atom.backtrackWatchers);
		atom.explanation = null;
		atom.decideStatus = null;
		atom.decideLevel = -1;
		atoms.add(atom);
		for (Theory t2: theories)
			t2.backtrackLiteral(literal);
		if (profileTime)
			backtrackTime += System.nanoTime() - time;
	}

	private Clause checkConsistency() {
		for (Theory t: theories) {
			Clause conflict = t.computeConflictClause();
			if (conflict != null)
				return conflict;
		}
		return null;
	}

	private Literal chooseLiteral() {
		DPLLAtom atom;
		Iterator<DPLLAtom> it = atoms.iterator(); 
		if (!it.hasNext())
			return null;
		atom = it.next();
		assert atom.decideStatus == null;
		//logger.debug("Choose literal: "+atom+" Weight "
		//		+ (atom.activity/factor) +" - last: " + atom.lastStatus);
		return atom.lastStatus == null ? atom.negate() : atom.lastStatus;
	}
	
	private static final int luby_super(int i) {
        int power;
        int k;
 
        assert i > 0;
        /* let 2^k be the least power of 2 >= (i+1) */
        k = 1;
        power = 2;
        while (power < (i + 1)) {
            k += 1;
            power *= 2;
        }
        if (power == (i + 1))
            return (power / 2);
        return (luby_super(i - (power / 2) + 1));
    }

	private void printStatistics() {
		logger.info("Confl: "+conflicts+" Props: "+props+
				" Tprops: "+tprops+" Decides: "+decides);
		logger.info("Times: Expl: "+explainTime+ " Prop: "+propTime
				+" Set: "+setTime+" Back: "+backtrackTime); 
		logger.info("Atoms: "+num_solvedatoms+"/"+(atoms.size()+ decideStack.size())+
				" Clauses: "+num_clauses+
				" Axioms: "+num_axiomclauses);
		for (Theory t: theories)
			t.printStatistics(logger);
	}
	
	public Formula[] getInterpolants() {
		return interpolants;
	}

	/**
	 * Solves the current problem.
	 * @return true if sat, false if unsat.
	 */
	public boolean solve() {
		computeInterpolants();
		int iteration = 1;
		int nextRestart = RESTART_FACTOR;
		long time; 
		long lastTime;
		if (profileTime)
			lastTime = System.nanoTime();
		while (true) {
			Clause conflict;
			do {
				conflict = propagate();
				if (conflict != null)
					break;
				Literal literal = chooseLiteral();
				if (literal == null) {
					conflict = checkConsistency();
					if (conflict == null
						&& changedList.isEmpty()
						&& atoms.isEmpty()) {
						/* We found a model */
						printStatistics();
						logger.info("Hooray, we found a model:");
						for (Theory t: theories)
							t.dumpModel(logger);
						return true;
					}
					continue;
				} else {
					currentDecideLevel++;
					decides++;
					conflict = setLiteral(literal);
				}
			} while (conflict == null);
			if (profileTime) {
				time = System.nanoTime();
				propTime += time - lastTime;
				lastTime = time;
			}
			Clause explanation = explainConflict(conflict);
			if (profileTime) {
				time = System.nanoTime();
				explainTime += time - lastTime;
				lastTime = time;
			}
			if (explanation.literals.length == 0) {
				printStatistics();
				logger.info("Formula is unsat");
				this.interpolants = new Formula[explanation.interpolants.length];
				FormulaUnFleterer unfleterer = new FormulaUnFleterer(smtTheory, true);
				for (int i = 0; i < interpolants.length; i++) {
					interpolants[i] = unfleterer.unflet(explanation.interpolants[i].interpolant);
					logger.info("Interpolant: "+interpolants[i]);
				}
				/*
				logger.info("Learned Clauses");
				for (Clause c : learnedClauses) {
					logger.info("Cl: len "+c.literals.length+ " used "+c.usedTimes + ": "+c);
				}
				*/
				return false;
			}
			if (atom_scale > LIMIT) {
				List<DPLLAtom> theAtoms = new ArrayList<DPLLAtom>(atoms);
				atoms.clear();
				for (DPLLAtom a : theAtoms) {
					a.activity *= Double.MIN_NORMAL;
					atoms.add(a);
				}
				for (Literal l : decideStack)
					l.getAtom().activity *= Double.MIN_NORMAL;
				atom_scale *= Double.MIN_NORMAL;
			}
			if (cls_scale > LIMIT) {
				Iterator<Clause> it = learnedClauses.iterator();
				while (it.hasNext()) {
					Clause c = it.next();
					c.activity *= Double.MIN_NORMAL;
				}
				cls_scale *= Double.MIN_NORMAL;
			}
			if (--nextRestart == 0) {
				while (decideStack.size() > num_solvedatoms) {
					Literal lit = decideStack.remove(decideStack.size()-1);
					Object litexpl = lit.getAtom().explanation;
					if (litexpl instanceof Clause) {
						((Clause) litexpl).activity += cls_scale;
						((Clause) litexpl).usedTimes++;
					}
					backtrackLiteral(lit);
				}
				Iterator<Clause> it = learnedClauses.iterator();
				while (it.hasNext()) {
					Clause c = it.next();
					if (c.activity < cls_scale * CLAUSE_UNLEARN_ACTIVITY) {
						if (c.firstWatch.next != null) {
							c.firstWatch.removeFromList();
							c.secondWatch.removeFromList();
							num_clauses--;
						}
						it.remove();
					}
				}
				currentDecideLevel = 0;
				iteration++;
				nextRestart = RESTART_FACTOR * luby_super(iteration);
				if (printStatistics)
					printStatistics();
			}
			if (profileTime) {
				lastTime = System.nanoTime();
			}
		}
	}

	public void addAtom(DPLLAtom atom) {
		atoms.add(atom);
	}

	public void addTheory(Theory t) {
		Theory[] newTheories = new Theory[theories.length+1];
		System.arraycopy(theories, 0, newTheories, 0, theories.length);
		newTheories[theories.length] = t;
		theories = newTheories;
	}

	public local.stalin.logic.Theory getSMTTheory() {
		return smtTheory;
	}

	public int getFormulaCount() {
		return numFormulas;
	}
	// TODO:Remove
	public void dumpClausesSMTLIB() {
		int nands = -1;
		StringBuilder sb = new StringBuilder();
		sb.append("(benchmark clausedump\n:logic ").append(smtTheory.getLogic());
		for (Sort s : smtTheory.getSorts()) {
			if (!s.isIntern())
				sb.append("\n:extrasorts((").append(s.getName()).append("))");
		}
		sb.append("\n:extrapreds (");
		for (PredicateSymbol ps : smtTheory.getPredicates()) {
			if (!ps.isIntern())
				sb.append(ps.toString());
		}
		sb.append(")\n:extrafuns (");
		for (FunctionSymbol fs : smtTheory.getFunctions()) {
			if (!fs.isIntern())
				sb.append(fs.toString());
		}
		sb.append(")\n:formula\n(and ");
		for( Clause.Watcher w : changedList ) {
			++nands;
			Clause c = w.getClause();
			if( c.getSize() > 1 )
				sb.append("(or ");
			for( int i = 0; i < c.getSize(); ++i ) {
				Literal l = c.getLiteral(i);
				Formula f = l.getSMTFormula(smtTheory);
				assert(f!= null);
				sb.append(f).append(' ');
			}
			sb.deleteCharAt(sb.length() - 1);
			if( c.getSize() > 1 )
				sb.append(")");
		}
		sb.append("))");
		//System.err.println(sb);
		try {
		java.io.FileWriter fw = new java.io.FileWriter("/tmp/clauses.smt");
		fw.write(sb.toString());
		fw.flush();
		fw.close();
		}catch(Throwable t) {}
	}

	public void incNumberOfFormulas() {
		numFormulas++;
	}
	public Logger getLogger() {
		return logger;
	}
}
