/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause.WatchList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CuckooHashSet;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * The DPLL engine.
 * @author hoenicke
 *
 */
public class DPLLEngine {
	private Logger logger;
	/* Completeness */
	public static final int COMPLETE = 0;
	public static final int INCOMPLETE_QUANTIFIER = 1;
	public static final int INCOMPLETE_THEORY = 2;
	public static final int INCOMPLETE_MEMOUT = 3;
	public static final int INCOMPLETE_UNKNOWN = 4;
	public static final int INCOMPLETE_TIMEOUT = 5;
	
	private static final String[] gcompletenessstrings = {
		"Complete",
		"Quantifier in Assertion Stack",
		"Theories with incomplete decision procedure used",
		"Not enough memory",
		"Unknown internal error",
		"Sat check timed out"
	};
	private int completeness;
	
	/* Incrementality */
	/**
	 * Number of active pushs.
	 */
	private int stacklevel = 0;
	/**
	 * The assertion stack data.
	 */
	private StackData m_ppStack;
	/**
	 * List of all input clauses. This list should not contain any learned clauses!
	 */
	private SimpleList<Clause> clauses = new SimpleList<Clause>();

	/**
	 * Empty clause. This is a cache that speeds up detecting unsatisfiability
	 * in the case our proof does not depend on a newly pushed formula.
	 */
	private Clause m_unsatClause = null;
	
	/* Statistics */
	private int conflicts, decides, tprops, props;
	private int num_solvedatoms, num_clauses, num_axiomclauses;
	private int num_insts;
	private int num_toplevelinsts;
	SimpleList<Clause> learnedClauses = new SimpleList<Clause>();
	private long propTime, propClauseTime, explainTime, setTime, checkTime, backtrackTime;
	private static final boolean printStatistics = true;
	private Theory smtTheory;
	private int m_numRandomSplits;
	
	private boolean mHasModel;
	private boolean mStopEngine;

	double atom_scale = 1 - 1.0/Config.ATOM_ACTIVITY_FACTOR;
	double cls_scale = 1 - 1.0/Config.CLS_ACTIVITY_FACTOR;
	
	/**
	 * The list of unit clauses that are not yet decided.
	 */
	WatchList watcherSetList = new WatchList();
	WatchList watcherBackList = new WatchList();
	
	ArrayList<Literal> decideStack = new ArrayList<Literal>();
	
	/**
	 * The list of all theories.
	 */
	private ITheory[] theories = new ITheory[0];
	private AtomQueue atoms = new AtomQueue();

	private int currentDecideLevel = 0;
	private boolean m_isPGenabled = false;
	private boolean m_produceAssignments = false;
	private ScopedHashMap<String, Literal> m_assignments;
	
	// Random source for the solver.
	private Random m_Random;
	
	public DPLLEngine(Theory smtTheory,Logger logger) {
		this.smtTheory = smtTheory;
		completeness = COMPLETE;
		assert(logger != null);
		this.logger = logger;
		m_ppStack = new StackData();
		// Benchmark sets the seed...
		m_Random = new Random();
	}
	
	public int getDecideLevel() {
		return currentDecideLevel;
	}
	
	public void insertPropagatedLiteral(ITheory t, Literal lit, int decideLevel) {
		assert (lit.getAtom().decideStatus == null);
		assert (!decideStack.contains(lit));
		assert (!decideStack.contains(lit.negate()));
		assert t != null : "Decision in propagation!!!";
		assert checkDecideLevel();
		int stackptr = decideStack.size();
		int level = currentDecideLevel;
		while (level > decideLevel) {
			DPLLAtom atom = decideStack.get(--stackptr).getAtom();
			if (atom.explanation == null)
				level--;
			atom.stackPosition++;
		}
		decideStack.add(stackptr, lit);
		DPLLAtom atom = lit.getAtom();
		// We have to tell the ppStack about this literal.  Otherwise it will
		// not be removed on a pop
		m_ppStack.addAtom(atom);
		assert !atoms.contains(atom);
		atom.decideLevel = decideLevel;
		atom.stackPosition = stackptr;
		atom.decideStatus = lit;
		atom.lastStatus = atom.decideStatus;
		atom.explanation = t;
		if (decideLevel == 0) {
			/* This atom is now decided once and for all. */
			num_solvedatoms++;
			generateLevel0Proof(lit);
		}
		assert checkDecideLevel();
	}
	
	public void insertPropagatedLiteralBefore(ITheory t, Literal lit, Literal beforeLit) {
		assert (decideStack.get(beforeLit.getAtom().getStackPosition()) == beforeLit);
		assert (beforeLit.getAtom().decideStatus == beforeLit);
		assert (beforeLit.getAtom().getStackPosition() >= 0);
		assert (lit.getAtom().decideStatus == null);
		assert (!decideStack.contains(lit));
		assert (!decideStack.contains(lit.negate()));
		assert t != null : "Decision in propagation!!!";
		assert checkDecideLevel();
		DPLLAtom beforeAtom = beforeLit.getAtom(); 
		int stackptr = beforeAtom.getStackPosition();
		int level = beforeAtom.getDecideLevel();
		if (beforeAtom.explanation == null)
			level--;
		decideStack.add(stackptr, lit);
		for(int i = stackptr+1; i < decideStack.size(); i++) {
			assert decideStack.get(i).getAtom().getStackPosition() == i-1;
			decideStack.get(i).getAtom().stackPosition = i;
		}
		DPLLAtom atom = lit.getAtom();
		// We have to tell the ppStack about this literal.  Otherwise it will
		// not be removed on a pop
		m_ppStack.addAtom(atom);
		assert !atoms.contains(atom);
		atom.decideLevel = level;
		atom.stackPosition = stackptr;
		atom.decideStatus = lit;
		atom.lastStatus = atom.decideStatus;
		atom.explanation = t;
		if (level == 0) {
			/* This atom is now decided once and for all. */
			num_solvedatoms++;
			generateLevel0Proof(lit);
		}
		assert checkDecideLevel();
	}
	/**
	 * Propagate unit clauses first in boolean part, then in 
	 * the theory part.
	 * @return a conflict clause if a conflict was detected.
	 */
	@SuppressWarnings("unused")
	private Clause propagateInternal() {
		
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
			long time = 0;
			if (Config.PROFILE_TIME)
				time = System.nanoTime();
			for (ITheory t: theories) {
				conflict = t.checkpoint();
				if (conflict != null) {
					return conflict;
				}
			}
			if (Config.PROFILE_TIME)
				checkTime += System.nanoTime() - time;

			conflict = propagateTheories();
			assert !Config.EXPENSIVE_ASSERTS || checkDecideLevel();
			if (conflict != null)
				return conflict;
			if (decideStack.size() == level)
				return null;
		}
	}
	
	private Clause propagateTheories() {
		while (true) {
			boolean changed = false;
			for (ITheory t: theories) {
				Literal propLit = t.getPropagatedLiteral();
				if (propLit != null) {
					do {
						if (propLit.atom.decideStatus == null) {
							tprops++;
							propLit.atom.explanation = t;
							Clause conflict = setLiteral(propLit);
							if (conflict != null) {
								for (Literal lit: conflict.m_literals) {
									DPLLAtom atom = lit.getAtom();
									assert(atom.decideStatus == lit.negate());
								}
								return conflict;
							}
						} else if (propLit.atom.decideStatus != propLit) {
							Clause conflict = t.getUnitClause(propLit);
							return conflict;
						}
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
		long time = 0;
		if (Config.PROFILE_TIME)
			time = System.nanoTime() - setTime;
		while (!watcherBackList.isEmpty()) {
			int index = watcherBackList.m_HeadIndex;
			Clause clause = watcherBackList.removeFirst();
			/* check if clause was already removed */
			if (clause.next == null) {
//				System.err.println("Found removed clause in progation: " + clause);
				continue;
			}
			Literal[] lits = clause.m_literals;
			Literal myLit = lits[index];
			Literal status = myLit.getAtom().decideStatus;
			/* Special case unit clause: propagate or return as conflict clause */
			if (lits.length == 1) {
				myLit.getAtom().backtrackWatchers.append(clause, index);
				if (status != myLit) {
					if (status == null) {
						/* Propagate the unit clause. */
						myLit.getAtom().explanation = clause;
						props++;
						clause = setLiteral(myLit);
					}
					if (Config.PROFILE_TIME)
						propClauseTime += System.nanoTime() - time - setTime;
					return clause;
				}
			} else if (status == myLit.negate()) {
				watcherSetList.append(clause, index);
			} else {
				myLit.watchers.append(clause, index);
			}
		}

		//logger.info("new set: "+watcherSetList.size());
	nextList:
		while (!watcherSetList.isEmpty()) {
			int index = watcherSetList.getIndex();
			Clause clause = watcherSetList.removeFirst();
			/* check if clause was already removed */
			if (clause.next == null) {
				continue nextList;
			}
			Literal[] lits = clause.m_literals;
			assert lits[index].getAtom().decideStatus == lits[index].negate();
			assert(lits.length >= 2);
			Literal otherLit = lits[1-index];
			DPLLAtom otherAtom = otherLit.getAtom(); 
			if (otherAtom.decideStatus == otherLit) {
				/* Other watcher is true, put ourself on
				 * the backtrack watcher list.
				 */
				otherAtom.backtrackWatchers.append(clause, index);
				continue nextList;
			}
			for (int i = 2; i < lits.length; i++) {
				Literal lit = lits[i];
					DPLLAtom atom = lit.getAtom();
				Literal status = atom.decideStatus;
				if (status != lit.negate()) {
					/* check if clause is too old to keep */
					if (clause.activity < cls_scale * Config.CLAUSE_UNLEARN_ACTIVITY
							&& status == null && clause.doCleanup(this)) {
						clause.removeFromList();
					} else {
						/* watch this literal */
						for (int j = i; j > 2; j--)
							lits[j] = lits[j-1];
						lits[2] = lits[index];
						lits[index] = lit;
						lit.watchers.append(clause, index);
					}
					continue nextList;
				}
			}
			/* Now we haven't found another atom to watch.  Hence we have
			 * a unit clause or conflict clause.
			 */
			// put the entry back into the watch list of the literal.  Until
			// the literal changes again, the watcher is not needed anymore.
			lits[index].watchers.append(clause, index);
			if (otherAtom.decideStatus == null) {
				/* Propagate the unit clause. */
				otherAtom.explanation = clause;
				props++;
				clause = setLiteral(otherLit);
				if (clause == null)
					clause = propagateTheories();
			}
			/* Conflict clause */
			if (Config.PROFILE_TIME)
				propClauseTime += System.nanoTime() - time - setTime;
			return clause;
		}
		if (Config.PROFILE_TIME)
			propClauseTime += System.nanoTime() - time - setTime;
		return null;
	}
	
	private boolean checkConflict(Clause conflict) {
		for (Literal lit: conflict.m_literals) {
			DPLLAtom a = lit.getAtom();
			assert(a.decideStatus == lit.negate());
		}
		return true;
	}
	
	/**
	 * Sets a literal to true and tells all theories about it.  The
	 * literal must be undecided when this function is called.
	 * @param literal the literal to set.
	 * @return a conflict clause if a conflict was detected.
	 */
	@SuppressWarnings("unused")
	private Clause setLiteral(Literal literal) {
		if (logger.isDebugEnabled())
			logger.debug("S " + literal);
		DPLLAtom atom = literal.getAtom();
		assert (atom.decideStatus == null);
		assert atoms.contains(atom);
		atom.stackPosition = decideStack.size();
		decideStack.add(literal);
		atom.decideLevel = currentDecideLevel;
		atom.decideStatus = literal;
		atom.lastStatus = atom.decideStatus;
		atoms.remove(atom);
		assert !Config.EXPENSIVE_ASSERTS || checkDecideLevel();
		watcherSetList.moveAll(literal.negate().watchers);
		long time;
		if (Config.PROFILE_TIME)
			time = System.nanoTime();
		Clause conflict = null;
		if (currentDecideLevel == 0) {
			/* This atom is now decided once and for all. */
			num_solvedatoms++;
			generateLevel0Proof(literal);
		}
		for (ITheory t: theories) {
			conflict = t.setLiteral(literal);
			if (conflict != null) {
				assert checkConflict(conflict);
				break;
			}
		}
		if (Config.PROFILE_TIME)
			setTime += System.nanoTime() - time;
		return conflict;
	}

	public void watchClause(Clause clause) {
		if (clause.getSize() <= 1) {
			if (clause.getSize() == 0) {
				if (m_unsatClause == null)
					m_unsatClause = clause;
			} else {
				/* propagate unit clause: only register watcher zero. */
				watcherBackList.append(clause, 0);
			}
		} else {
			/* A clause is "watched" if it appears on either the
			 * watcherBack/SetList or the watchers list of some atom.
			 */
			watcherBackList.append(clause, 0);
			watcherBackList.append(clause, 1);
		}
	}

	public void addClause(Clause clause) {
		atom_scale += 1.0-(1.0/Config.ATOM_ACTIVITY_FACTOR);
		clause.activity = Double.POSITIVE_INFINITY;
		num_axiomclauses++;
		assert (clause.stacklevel == stacklevel);
		clauses.prepend(clause);
		watchClause(clause);
	}
	
	void removeClause(Clause c) {
		c.removeFromList();
	}

	public void addFormulaClause(Literal[] literals, ProofNode proof) {
		addFormulaClause(literals, proof, null);
	}
	
	public void addFormulaClause(
			Literal[] literals, ProofNode proof, ClauseDeletionHook hook) {
		Clause clause = new Clause(literals, stacklevel);
		clause.setDeletionHook(hook);
		addClause(clause);
		if (isProofGenerationEnabled()) {
			clause.setProof(proof);
		}
		logger.trace(new DebugMessage("Added clause {0}", clause));
	}
	
	public void learnClause(Clause clause) {
		atom_scale += 1.0-(1.0/Config.ATOM_ACTIVITY_FACTOR);
		num_clauses++;
		clause.activity = cls_scale;//Double.POSITIVE_INFINITY;
		if (clause.getSize() <= 2)
			clause.activity = Double.POSITIVE_INFINITY;
		learnedClauses.append(clause);
		watchClause(clause);
	}
	
//	public void addInstantiationClause(Literal[] lits) {
//		++num_insts;
//		Clause clause = new Clause(lits);
//		addClause(clause);
//		if (isProofGenerationEnabled()) {
//			// FIXME: This should somehow be related to the instantiation
//			LeafNode ln = new LeafNode(LeafNode.QUANT_INST, null, false);
//			clause.setProof(ln);
//		}
//	}
	
	private boolean checkDecideLevel() {
		int decision = 0;
		int i = 0;
		for (Literal lit : decideStack) {
			if (lit.getAtom().explanation == null)
				decision++;
			assert lit.getAtom().stackPosition == i;
			assert lit.getAtom().decideLevel == decision;
			i++;
		}
		return decision == currentDecideLevel;
	}
	
	private int countLitsOnDecideLevel(Set<Literal> conflict) {
		int numLits = 0;
		int stackPtr = decideStack.size();
		while (true) {
			Literal lit = decideStack.get(--stackPtr);
			assert(!conflict.contains(lit.negate()));
			if (conflict.contains(lit))
				numLits++;
			if (lit.getAtom().explanation == null)
				return numLits;
		}
	}
	
	private Clause explainConflict(Clause clause) {
		if (logger.isDebugEnabled())
			logger.debug("explain conflict "+clause);
		List<Antecedent> antecedents = null;
		HashSet<Literal> level0Ants = null;
		if (isProofGenerationEnabled()) {
			antecedents = new ArrayList<Antecedent>();
			level0Ants = new HashSet<Literal>();
		}
		int expstacklevel = clause.stacklevel;
		conflicts++;
		assert checkDecideLevel();
		atom_scale *= Config.ATOM_ACTIVITY_FACTOR;
		cls_scale *= Config.CLS_ACTIVITY_FACTOR;
		Set<Literal> conflict = new CuckooHashSet<Literal>();
		int maxDecideLevel = 1;
		int numLitsOnMaxDecideLevel = 0;
		for (Literal lit: clause.m_literals) {
			DPLLAtom atom = lit.getAtom();
			assert(atom.decideStatus == lit.negate());
			if (atom.decideLevel > 0) {
				if (atom.decideLevel >= maxDecideLevel) {
					if (atom.decideLevel > maxDecideLevel) {
						maxDecideLevel = atom.decideLevel;
						numLitsOnMaxDecideLevel = 1;
					} else
						numLitsOnMaxDecideLevel++;
				}
				conflict.add(lit.negate());
			} else {
				expstacklevel = level0resolve(lit, level0Ants, expstacklevel);
			}
			atom.activity += atom_scale;
		}
		if (logger.isDebugEnabled())
			logger.debug("removing level0: "+conflict);
		if (conflict.size() == 0) {
			/* Unsatisfiable
			 */
			Clause res = new Clause(new Literal[0], expstacklevel);
			if (isProofGenerationEnabled()) {
				for (Literal l0: level0Ants)
					antecedents.add(new Antecedent(l0, getLevel0(l0)));
				Antecedent[] ants = 
					antecedents.toArray(new Antecedent[antecedents.size()]);
				res.setProof(new ResolutionNode(clause, ants));
			}
			return res;
		}
		assert numLitsOnMaxDecideLevel >= 1;
		while (currentDecideLevel > maxDecideLevel) {
			Literal lit = decideStack.remove(decideStack.size()-1);
			assert(!conflict.contains(lit.negate()));
			assert !conflict.contains(lit);
			if (lit.getAtom().explanation == null)
				decreaseDecideLevel();
			assert checkDecideLevel();
			backtrackLiteral(lit);
			assert checkDecideLevel();
		}
		while (numLitsOnMaxDecideLevel > 1) {
			assert checkDecideLevel();
			assert currentDecideLevel == maxDecideLevel;
			assert countLitsOnDecideLevel(conflict) == numLitsOnMaxDecideLevel;
			assert checkDecideLevel();
			Literal lit = decideStack.get(decideStack.size()-1);
			assert(!conflict.contains(lit.negate()));
			if (!conflict.contains(lit)) {
				assert lit.getAtom().explanation != null;
				assert checkDecideLevel();
				decideStack.remove(decideStack.size()-1);
				backtrackLiteral(lit);
				assert checkDecideLevel();
				continue;
			}
			
			/* Do a resolution step with explanation */
			Clause expl = getExplanation(lit);
			expl.activity += cls_scale;
//			expl.usedTimes++;
			expstacklevel = Math.max(expstacklevel,expl.stacklevel);
			if (isProofGenerationEnabled()) {
				antecedents.add(new Antecedent(lit,expl));
			}
			decideStack.remove(decideStack.size()-1);
			backtrackLiteral(lit);
			assert checkDecideLevel();
			conflict.remove(lit);
			numLitsOnMaxDecideLevel--;
			DPLLAtom atom = lit.getAtom();
			if (logger.isDebugEnabled())
				logger.debug("Resolving with " + expl + " pivot = " + atom);
			for (Literal l : expl.m_literals) {
				if (l != lit) {
					assert(l.getAtom().decideStatus == l.negate());
					int level = l.getAtom().decideLevel;
					if (level > 0) {
						if (conflict.add(l.negate()) && level == maxDecideLevel)
							numLitsOnMaxDecideLevel++;
					} else {
						// Here, we do level0 resolution as well
						expstacklevel = 
							level0resolve(l, level0Ants, expstacklevel);
					}
					l.getAtom().activity += atom_scale;
				}
			}
			assert countLitsOnDecideLevel(conflict) == numLitsOnMaxDecideLevel;
			if (logger.isDebugEnabled()) {
				logger.debug("new conflict: "+conflict);
			}
		}
		assert currentDecideLevel == maxDecideLevel;
		assert countLitsOnDecideLevel(conflict) == numLitsOnMaxDecideLevel;
		assert numLitsOnMaxDecideLevel == 1;
		while (currentDecideLevel >= maxDecideLevel) {
			Literal lit = decideStack.remove(decideStack.size()-1);
			assert(!conflict.contains(lit.negate()));
			if (lit.getAtom().explanation == null)
				decreaseDecideLevel();
			assert checkDecideLevel();
			backtrackLiteral(lit);
			assert checkDecideLevel();
		}
		/* We removed at least one decision point.
		 * Try to backtrack further.
		 */
		if (Config.DEEP_BACKTRACK)
			findBacktrackingPoint(conflict);
		
		if (logger.isDebugEnabled())
			logger.debug("Backtrack to "+decideStack.size());

		HashMap<Literal, Integer> redundancy = computeRedundancy(conflict);
		Integer REDUNDANT = 1;

		int stackPtr = decideStack.size();
		while (stackPtr > num_solvedatoms) {
			Literal lit = decideStack.get(--stackPtr);
			if (redundancy.get(lit) == REDUNDANT && conflict.contains(lit)) {
				/* Do a resolution step with explanation */
				Clause expl = getExplanation(lit);
				expl.activity += cls_scale;
//				expl.usedTimes++;
				expstacklevel = Math.max(expstacklevel,expl.stacklevel);
				if (isProofGenerationEnabled()) {
					antecedents.add(new Antecedent(lit,expl));
				}
				conflict.remove(lit);
				for (Literal l : expl.m_literals) {
					if (l != lit) {
						assert(l.getAtom().decideStatus == l.negate());
						int level = l.getAtom().decideLevel;
						if (level > 0) {
							conflict.add(l.negate());
						} else {
							// Here, we do level0 resolution as well
							expstacklevel =
								level0resolve(l, level0Ants, expstacklevel);
						}
						l.getAtom().activity += atom_scale;
					}
				}
			}
		}
		if (logger.isDebugEnabled())
			logger.debug("removing redundancy yields "+conflict);
		Literal[] newlits = new Literal[conflict.size()];
		int i = 0;
		for (Literal l : conflict) {
			newlits[i++] = l.negate();
		}
		assert newlits[newlits.length-1] != null;
		Clause resolution = new Clause(newlits, expstacklevel);
		if (isProofGenerationEnabled()) {
			for (Literal l0: level0Ants)
				antecedents.add(new Antecedent(l0, getLevel0(l0)));
			if (!antecedents.isEmpty()) {
				Antecedent[] ants = 
					antecedents.toArray(
							new Antecedent[antecedents.size()]);
				resolution.setProof(new ResolutionNode(clause, ants));
			} else {
				// TODO: only one clause object needed here.
				resolution.setProof(clause.getProof());
			}
		}
		if (logger.isDebugEnabled())
			logger.debug("Resolved to " + resolution);
		return resolution;
	}
	
	private final int level0resolve(Literal l, Set<Literal> level0Ants, int sl) {
		Clause l0 = getLevel0(l.negate());
		if (isProofGenerationEnabled()) {
			level0Ants.add(l.negate());
		}
		return (l0.stacklevel > sl) ? l0.stacklevel : sl;
	}
		
	private Clause getExplanation(Literal lit) {
		Object explanation = lit.getAtom().explanation;
		if (explanation instanceof ITheory) {
			Clause expl = ((ITheory) explanation).getUnitClause(lit);
			lit.getAtom().explanation = expl;
			assert(checkUnitClause(expl,lit));
			assert checkDecideLevel();
			return expl;
		} else {
			assert explanation == null || (checkUnitClause((Clause)explanation,lit));
			return (Clause) explanation;
		}
	}

	private HashMap<Literal, Integer> computeRedundancy(Set<Literal> conflict) {
		Integer REDUNDANT = 1;
		Integer FAILED = 2;
		Integer KEEP = 3;
		HashMap<Literal,Integer> status = new HashMap<Literal, Integer>();
		for (Literal l : conflict) {
			if (l.getAtom().getDecideStatus() != null) {
				assert l.getAtom().getDecideStatus() == l;
				status.put(l, REDUNDANT);
			}
		}
		ArrayDeque<Literal> todo = new ArrayDeque<Literal>();
		Iterator<Literal> it = conflict.iterator();
	litloop:
		while (it.hasNext()) {
			Literal lit = it.next();
			if (lit.getAtom().getDecideStatus() == null)
				continue;
			todo.addFirst(lit);
		todoloop:
			while (!todo.isEmpty()) {
				Literal next = todo.getFirst();
				assert next.getAtom().getDecideStatus() == next;
				Clause expl = getExplanation(next);
				//logger.info("check "+next+" expl "+expl);
				if (expl == null) {
					while(todo.size() > 1)
						status.put(todo.removeFirst(), FAILED);
					status.put(todo.removeFirst(), KEEP);
					continue litloop;
				}
				for (Literal l : expl.m_literals) {
					assert l.getAtom().getDecideStatus() != null;
					if (l != next && l.getAtom().getDecideLevel() > 0) {
						Literal lneg = l.negate();
						assert lneg.getAtom().getDecideStatus() == lneg;
						Integer st = status.get(lneg);
						if (st == FAILED) {
							while(todo.size() > 1)
								status.put(todo.removeFirst(), FAILED);
							status.put(todo.removeFirst(), KEEP);
							continue litloop;
						} else if (st == null) {
							todo.addFirst(lneg);
							continue todoloop;
						}
					}
				}
				status.put(todo.removeFirst(), REDUNDANT);
			}
		}
		return status;
	}

	private boolean checkUnitClause(Clause unit, Literal lit) {
		boolean found = false;
		for (Literal l : unit.m_literals) {
			assert l != lit.negate() : "Negation of unit literal in explanation";
			if (l == lit) {
				found = true;
			} else {
				assert l.atom.decideStatus == l.negate()
			        && l.atom.getStackPosition() < lit.getAtom().getStackPosition() :
				 		"Not a unit clause: " + l + " in " + unit;
			}
		}
		assert found : "Unit literal not in explanation";
		return found;
	}

	private Clause finalizeBacktrack() {
		watcherBackList.moveAll(watcherSetList);
		for (ITheory t: theories) {
			Clause conflict = t.backtrackComplete();
			if (conflict != null)
				return conflict;
		}
		return null;
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
				decreaseDecideLevel();
			}
		}
	}

	private void backtrackLiteral(Literal literal) {
		long time;
		if (logger.isDebugEnabled())
			logger.debug("B " + literal);
		DPLLAtom atom = literal.getAtom();
		watcherBackList.moveAll(atom.backtrackWatchers);
		atom.explanation = null;
		atom.decideStatus = null;
		atom.decideLevel = -1;
		atom.stackPosition = -1;
		atoms.add(atom);
		if (Config.PROFILE_TIME)
			time = System.nanoTime();
		for (ITheory t2: theories)
			t2.backtrackLiteral(literal);
		if (Config.PROFILE_TIME)
			backtrackTime += System.nanoTime() - time;
	}

	private Clause checkConsistency() {
		long time = 0;
		if (Config.PROFILE_TIME)
			time = System.nanoTime();
		for (ITheory t: theories) {
			Clause conflict = t.computeConflictClause();
			if (conflict != null) {
				return conflict;
			}
		}
		if (Config.PROFILE_TIME)
			checkTime += System.nanoTime() - time;
		return null;
	}

	private Literal chooseLiteral() {
		DPLLAtom atom;
		int ran = m_Random.nextInt(Config.RANDOM_SPLIT_BASE);
		if (!atoms.isEmpty() && ran <= Config.RANDOM_SPLIT_FREQ) {
			atom = atoms.m_atoms[m_Random.nextInt(atoms.size())];
			++m_numRandomSplits;
		} else
			atom = atoms.peek();
		if (atom == null)
			return null;
		assert atom.decideStatus == null;
		//logger.debug("Choose literal: "+atom+" Weight "
		//		+ (atom.activity/factor) +" - last: " + atom.lastStatus);
//		return atom.lastStatus == null ? atom.negate() : atom.lastStatus;
		return atom.getPreferredStatus();
	}
	
	private static final int luby_super(int i) {
        int power;
 
        assert i > 0;
        /* let 2^k be the least power of 2 >= (i+1) */
        power = 2;
        while (power < (i + 1)) {
            power *= 2;
        }
        if (power == (i + 1))
            return (power / 2);
        return (luby_super(i - (power / 2) + 1));
    }

	private void printStatistics() {
		if (logger.isInfoEnabled()) {
			logger.info("Confl: "+conflicts+" Props: "+props+
					" Tprops: "+tprops+" Decides: "+decides+" RSplits: " + m_numRandomSplits);
			if (Config.PROFILE_TIME)
				logger.info("Times: Expl: "+(explainTime/1000/1000.0)+ " Prop: "+(propTime/1000/1000.0)
						+" PropClause: "+(propClauseTime/1000/1000.0) 
						+" Set: "+(setTime/1000/1000.0)+" Check: "+(checkTime/1000/1000.0) 
						+" Back: "+(backtrackTime/1000/1000.0));
			logger.info("Atoms: "+num_solvedatoms+"/"+(atoms.size()+ decideStack.size())+
					" Clauses: "+num_clauses+
					" Axioms: "+num_axiomclauses);
			logger.info("QI: " + (num_insts + num_toplevelinsts) + " total ("
					+ num_toplevelinsts + "/" + num_insts + ")");
			for (ITheory t: theories)
				t.printStatistics(logger);
		}
	}
	
	/**
	 * Solves the current problem.
	 * @return true if sat, false if unsat.
	 */
	public boolean solve() {
		mHasModel = false;
		mStopEngine = false;
		if (m_unsatClause != null) {
			logger.debug("Using cached unsatisfiability");
			return false;
		}
		try {
			if (Config.INITIAL_PHASE_BIAS_JW) {
				// Compute for all remaining atoms an initial polarity according
				// to Jeruslaw Wang
				Map<Literal, Double> scores = new HashMap<Literal, Double>();
				clause_loop: for (Clause c : clauses) {
					double inc = 1.0;
					for (Literal lit : c.m_literals) {
						Literal ds = lit.getAtom().getDecideStatus();
						if (ds == lit)
							// clause is satisfied
							continue clause_loop;
						if (ds != lit.negate())
							inc /= 2.0;
					}
					// Here, clause is not satisfied
					for (Literal lit : c.m_literals) {
						Literal ds = lit.getAtom().getDecideStatus();
						if (ds != lit.negate()) {
							Double score = scores.get(lit);
							if (score == null)
								scores.put(lit, inc);
							else
								scores.put(lit, score + inc);
						}
					}
				}
				for (DPLLAtom atom : atoms) {
					Double pscore = scores.get(atom);
					Double nscore = scores.get(atom.negate());
					double Pscore = pscore == null ? 0 : pscore;
					double Nscore = nscore == null ? 0 : nscore;
					atom.setPreferredStatus(
							Pscore > Nscore ? atom : atom.negate());
				}
			}
			int iteration = 1;
			int nextRestart = Config.RESTART_FACTOR;
			long time; 
			long lastTime;
			if (Config.PROFILE_TIME)
				lastTime = System.nanoTime() - setTime - backtrackTime;
			for (ITheory t : theories) {
				Clause conflict = t.startCheck();
				while (conflict != null) {
					conflict = explainConflict(conflict);
					learnClause(conflict);
					if (m_unsatClause != null)
						return false;
					conflict = finalizeBacktrack();
				}
			}
			while (!mStopEngine) {
				Clause conflict;
				do {
					conflict = propagateInternal();
					if (conflict != null || mStopEngine)
						break;
					if (Config.PROFILE_TIME) {
						time = System.nanoTime();
						propTime += time - lastTime - setTime - backtrackTime;
						lastTime = time - setTime - backtrackTime;
					}
					Literal literal = chooseLiteral();
					if (literal == null) {
						conflict = checkConsistency();
						if (conflict == null) {
							Literal lit = suggestions();
							if (lit != null) {
								if (lit.getAtom().explanation == null) {
									increaseDecideLevel();
									decides++;
								}
								conflict = setLiteral(lit);
							} else if (watcherBackList.isEmpty() && atoms.isEmpty()) {
								/* We found a model */
								if (logger.isInfoEnabled()) {
									printStatistics();
									logger.info("Hooray, we found a model:");
									for (ITheory t: theories)
										t.dumpModel(logger);
									for (Literal dlit : decideStack)
										logger.trace(new DebugMessage("{0}: {1}", dlit.hashCode(), dlit));
								}
								mHasModel = true;
								return true;
							}
						}
					} else {
						increaseDecideLevel();
						decides++;
						conflict = setLiteral(literal);
					}
				} while (conflict == null && !mStopEngine);
				while (conflict != null) {
					if (Config.PROFILE_TIME) {
						time = System.nanoTime();
						propTime += time - lastTime - setTime - backtrackTime;
						lastTime = time - setTime - backtrackTime;
					}
					Clause explanation = explainConflict(conflict);
					learnClause(explanation);
					if (m_unsatClause != null) {
						printStatistics();
						logger.info("Formula is unsat");
						/*
						logger.info("Learned Clauses");
						for (Clause c : learnedClauses) {
							logger.info("Cl: len "+c.literals.length+ " used "+c.usedTimes + ": "+c);
						}
						*/
						if (Config.PROFILE_TIME) {
							time = System.nanoTime();
							explainTime += time - lastTime - setTime - backtrackTime;
							lastTime = time - setTime - backtrackTime;
						}
						return false;
					}
					conflict = finalizeBacktrack();
					if (Config.PROFILE_TIME) {
						time = System.nanoTime();
						explainTime += time - lastTime - setTime - backtrackTime;
						lastTime = time - setTime - backtrackTime;
					}
				}
				if (atom_scale > Config.LIMIT) {
					for (DPLLAtom a : atoms) {
						a.activity *= Double.MIN_NORMAL;
					}
					for (Literal l : decideStack)
						l.getAtom().activity *= Double.MIN_NORMAL;
					atom_scale *= Double.MIN_NORMAL;
				}
				if (cls_scale > Config.LIMIT) {
					Iterator<Clause> it = learnedClauses.iterator();
					while (it.hasNext()) {
						Clause c = it.next();
						c.activity *= Double.MIN_NORMAL;
					}
					cls_scale *= Double.MIN_NORMAL;
				}
				if (--nextRestart == 0) {
					DPLLAtom next = atoms.peek();
					int restartpos = -1;
					for (int i = num_solvedatoms; i < decideStack.size(); ++i) {
						DPLLAtom var = decideStack.get(i).getAtom();
						if (var.explanation == null) {
							// This has been a decision
							if (var.activity < next.activity) {
								restartpos = i;
								break;
							}
								
						}
					}
					int decleveldec = 0;
					if (restartpos != -1) {
						while (decideStack.size() > restartpos) {
							Literal lit = decideStack.remove(decideStack.size()-1);
							assert(lit.getAtom().decideLevel != 0);
							Object litexpl = lit.getAtom().explanation;
							if (litexpl == null)
								++decleveldec;
							if (litexpl instanceof Clause) {
								((Clause) litexpl).activity += cls_scale;
//								((Clause) litexpl).usedTimes++;
							}
							backtrackLiteral(lit);
						}
					}
					unlearnClauses(stacklevel);
					conflict = finalizeBacktrack();
					assert (conflict == null);
					currentDecideLevel -= decleveldec;
					iteration++;
					for (ITheory t : theories)
						t.restart(iteration);
					nextRestart = Config.RESTART_FACTOR * luby_super(iteration);
					if (printStatistics) {
						logger.info("Restart");
						printStatistics();
					}
				}
				if (Config.PROFILE_TIME) {
					lastTime = System.nanoTime() - setTime - backtrackTime;
				}
			}
			return true;
		} catch (OutOfMemoryError oom) {
			// BUGFIX: Don't do this.  It will throw another OOM!
//			logger.fatal("Out of Memory during check", oom);
			completeness = INCOMPLETE_MEMOUT;
		} catch (Throwable t) {
			logger.fatal("Unknown exception during check",t);
			completeness = INCOMPLETE_UNKNOWN;
		}
		return true;
	}
	
	private final void unlearnClauses(int targetstacklevel) {
		Iterator<Clause> it = learnedClauses.iterator();
		while (it.hasNext()) {
			Clause c = it.next();
			if ((c.activity < cls_scale * Config.CLAUSE_UNLEARN_ACTIVITY ||
					c.stacklevel > targetstacklevel && c.doCleanup(this))) {
				num_clauses--;
				it.remove();
			}
		}
	}

	private Literal suggestions() {
		for (ITheory t : theories) {
			Literal lit = t.getPropagatedLiteral();
			if (lit != null) {
				lit.atom.explanation = t;
				assert(lit.getAtom().decideStatus == null);
				return lit;
			}
		}
		for (ITheory t : theories) {
			Literal lit = t.getSuggestion();
			if (lit != null) {
				assert(lit.getAtom().decideStatus == null);
				return lit;
			}
		}
		return null;
	}

	public void addAtom(DPLLAtom atom) {
		atoms.add(atom);
		m_ppStack.addAtom(atom);
	}
	
	public void removeAtom(DPLLAtom atom) {
		assert(atom.decideStatus == null);
		atoms.remove(atom);
		for (ITheory t : theories)
			t.removeAtom(atom);
	}

	public void addTheory(ITheory t) {
		ITheory[] newTheories = new ITheory[theories.length+1];
		System.arraycopy(theories, 0, newTheories, 0, theories.length);
		newTheories[theories.length] = t;
		theories = newTheories;
	}
	
	public void removeTheory() {
		ITheory[] newTheories = new ITheory[theories.length - 1];
		System.arraycopy(theories, 0, newTheories, 0, theories.length);
		theories = newTheories;
	}

	public Theory getSMTTheory() {
		return smtTheory;
	}

	public String dumpClauses() {
		StringBuilder sb = new StringBuilder();
		for (Clause c : clauses) {
			sb.append("(assert ");
			Literal[] lits = c.m_literals;
			if (lits.length == 1) {
				sb.append(lits[0].getSMTFormula(smtTheory)).append(")\n");
			} else {
				sb.append("(or");
				for (Literal l : lits) {
					sb.append(' ').append(l.getSMTFormula(smtTheory));
				}
				sb.append("))\n");
			}
		}
		return sb.toString();
	}
	
	public void setCompleteness(int ncompleteness) {
		completeness = ncompleteness;
	}
	public int getCompleteness() {
		return completeness;
	}
	public String getCompletenessReason() {
		return gcompletenessstrings[completeness];
	}
	public void push() {
		m_ppStack = m_ppStack.save(this);
		if (m_assignments != null) {
			m_assignments.beginScope();
		}
		++stacklevel;
	}
	public void pop(int numpops) {
		if (numpops < 1 || numpops > stacklevel)
			throw new IllegalArgumentException(
				"Must pop a positive number less than the current stack level");
		int targetstacklevel = stacklevel - numpops;
		if (m_unsatClause != null && m_unsatClause.stacklevel > targetstacklevel) {
			m_unsatClause = null;
		}
		if (!Config.EXPENSIVE_ASSERTS && 
				!checkProofStackLevel(m_unsatClause, targetstacklevel))
			throw new AssertionError();
		if (!decideStack.isEmpty()) {
			java.util.ListIterator<Literal> literals = 
				decideStack.listIterator(decideStack.size());
			while (literals.hasPrevious()) {
				Literal lit = literals.previous();
				Object litexpl = lit.getAtom().explanation;
				if (litexpl instanceof Clause) {
					((Clause) litexpl).activity += cls_scale;
//					((Clause) litexpl).usedTimes++;
				}
				backtrackLiteral(lit);
			}
			decideStack.clear();
			Clause conflict = finalizeBacktrack();
			assert (conflict == null);
		}
		unlearnClauses(targetstacklevel);
		currentDecideLevel = 0;
		num_solvedatoms = 0;
		Iterator<Clause> inputit = clauses.iterator();
		while (inputit.hasNext()) {
			Clause input = inputit.next();
			if (input.stacklevel > targetstacklevel) {
				if (input.doCleanup(this))
					inputit.remove();
				else
					throw new InternalError(
							"Input clause still blocked, but invalid");
//				logger.debug(new DebugMessage("Removed clause {0}",input));
			} else {
				// Terminate iteration here since only clauses with lower
				// stacklevel remain.
				break;
//				logger.debug(new DebugMessage("Keeping input {0}",input));
			}
		}
		for (int i = 0; i < numpops; ++i)
			m_ppStack = m_ppStack.restore(this, stacklevel - i - 1);
		stacklevel = targetstacklevel;
		if (m_assignments != null) {
			for (int i = 0; i < numpops; ++i) {
				if (m_assignments.getActiveScopeNum() == 1)
					break;
				m_assignments.endScope();
			}
		}
	}
	public Logger getLogger() {
		return logger;
	}
	
	public void showClauses(PrintWriter pw) {
		SimpleListable<Clause> c = clauses.next;
		while (c != clauses) {
			pw.println(c);
			c = c.next;
		}
	}

	public boolean hasModel() {
		return mHasModel && completeness == COMPLETE;
	}
	public void stop() {
		mStopEngine = true;
	}
	public void setProofGeneration(boolean enablePG) {
		m_isPGenabled = enablePG;
	}
	
	public boolean isProofGenerationEnabled() {
		return m_isPGenabled;
	}
	
	public Clause getProof() {
		return m_unsatClause;
	}
	
	private void generateLevel0Proof(Literal lit) {
		assert (lit.getAtom().decideLevel == 0) : "Level0 proof for non-level0 literal?";
		Clause c = getExplanation(lit);
		if (c.getSize() > 1) {
			int stacklvl = c.stacklevel; 
			Literal[] lits = c.m_literals;
			Clause res;
			if (isProofGenerationEnabled()) {
				Antecedent[] ants = new Antecedent[c.getSize() - 1];
				int i = 0;
				for (Literal l : lits) {
					if (l != lit) {
						Clause lc = getLevel0(l.negate());
						ants[i++] = new Antecedent(l.negate(), lc);
						stacklvl = Math.max(stacklvl, lc.stacklevel);
					}
				}
				res = new Clause(new Literal[] {lit}, new ResolutionNode(c, ants), stacklvl);
			} else {
				for (Literal l : lits) {
					if (l != lit) {
						Clause lc = getLevel0(l.negate());
						stacklvl = Math.max(stacklvl, lc.stacklevel);
					}
				}
				res = new Clause(new Literal[] {lit}, stacklvl);
			}
			lit.getAtom().explanation = res;
		}
	}
	
	private Clause getLevel0(Literal lit) {
		assert(lit.getAtom().decideLevel == 0);
		Object expl = lit.getAtom().explanation;
		assert expl instanceof Clause
		   && ((Clause)expl).getSize() == 1;
		assert ((Clause)expl).contains(lit);
		return (Clause)expl;
	}
	
	private final void increaseDecideLevel() {
		if (logger.isDebugEnabled())
			logger.debug("Decide@"+decideStack.size());
		currentDecideLevel++;
		assert(currentDecideLevel >= 0) : "Decidelevel negative";
		for (ITheory t : theories) {
			t.increasedDecideLevel(currentDecideLevel);
		}
	}
	private final void decreaseDecideLevel() {
		currentDecideLevel--;
		assert(currentDecideLevel >= 0) : "Decidelevel negative";
		for (ITheory t : theories) {
			t.decreasedDecideLevel(currentDecideLevel);
		}
	}

	public void topLevelMatch() {
		++num_toplevelinsts;
	}

	public ITheory[] getAttachedTheories() {
		return theories;
	}

	public int getAssertionStackLevel() {
		return stacklevel;
	}
	
	public boolean inconsistent() {
		return m_unsatClause != null;
	}
	
	private boolean checkProofStackLevel(Clause c, int targetlvl) {
		if (c == null || c.proof == null)
			return true;
		if (c.stacklevel > targetlvl) {
			System.err.println("Clause " + c + " above target level!");
			return false;
		}
		for (Literal lit : c.m_literals) {
			if (lit.getAtom().assertionstacklevel > targetlvl) {
				System.err.println("Literal " + lit + " in clause " + c + " above target level");
				return false;
			}
		}
		if (c.proof instanceof ResolutionNode) {
			ResolutionNode rn = (ResolutionNode) c.proof;
			if (!checkProofStackLevel(rn.getPrimary(), targetlvl))
				return false;
			for (Antecedent ante : rn.getAntecedents())
				if (!checkProofStackLevel(ante.antecedent, targetlvl))
					return false;
		}
		return true;
	}

	public Object getStatistics() {
		// Don't crash the solver one stupid scripts...
		Object[] res = theories == null ? new Object[1] :
			new Object[theories.length + 1];
		Object[] mystats = new Object[][] {
				{"Conflicts", conflicts},
				{"Propagations", props},
				{"Theory_propagations", tprops},
				{"Decides", decides},
				{"Random_splits", m_numRandomSplits},
				{"Num_Atoms", atoms.size()+decideStack.size()},
				{"Solved_Atoms", num_solvedatoms},
				{"Clauses", num_clauses},
				{"Axioms", num_axiomclauses},
				{"Times", new Object[][]{
						{"Explain", explainTime},
						{"Propagation", propTime},
						{"Set", setTime},
						{"Check", checkTime},
						{"Backtrack", backtrackTime}}
				}
		};
		res[0] = new Object[]{":Core", mystats};
		for (int i = 1; i < res.length; ++i) {
			res[i] = theories[i-1].getStatistics();
		}
		return res;
	}

	public void setProduceAssignments(boolean value) {
		boolean old = m_produceAssignments;
		m_produceAssignments = value;
		if (old != m_produceAssignments) {
			if (old)
				m_assignments = null;
			else
				m_assignments = new ScopedHashMap<String, Literal>();
		}
	}
	
	public boolean isProduceAssignments() {
		return m_produceAssignments;
	}

	public void trackAssignment(String label, Literal literal) {
		m_assignments.put(label, literal);
	}
	
	public Assignments getAssignments() {
		if (!m_produceAssignments)
			return null;
		HashMap<String, Boolean> assignment =
			new HashMap<String, Boolean>(m_assignments.size(), 1.0f);
		for (Map.Entry<String, Literal> me : m_assignments.entrySet()) {
			assignment.put(me.getKey(),
					me.getValue().getAtom().decideStatus == me.getValue());
		}
		return new Assignments(assignment);
	}

	/**
	 * Run a quick and incomplete check on the current context.  This only uses
	 * propagations and a conflict explanation to the empty clause.
	 * @return <code>false</code> if and only if the empty clause could be 
	 * 			derived. 
	 */
	public boolean quickCheck() {
		if (m_unsatClause != null)
			return false;
		Clause conflict = propagateInternal();
		while (conflict != null) {
			conflict = explainConflict(conflict);
			learnClause(conflict);
			if (m_unsatClause != null)
				return false;
			conflict = finalizeBacktrack();
		}
		return true;
	}
	
	/**
	 * Propagate as much as possible.  In contrast to {@link #quickCheck()},
	 * this function tells the theory solvers to start a check.  This might get
	 * more propagations than {@link #quickCheck()}.
	 * @return <code>false</code> if and only if the empty clause could be
	 *         derived.
	 */
	public boolean propagate() {
		if (m_unsatClause != null)
			return false;
		Clause conflict = null;
		for (ITheory t : theories) {
			conflict = t.startCheck();
			if (conflict != null)
				break;
		}
		if (conflict == null)	
			conflict = propagateInternal();
		while (conflict != null) {
			conflict = explainConflict(conflict);
			learnClause(conflict);
			if (m_unsatClause != null) {
				for (ITheory t : theories)
					t.endCheck();
				return false;
			}
			conflict = finalizeBacktrack();
		}
		for (ITheory t : theories)
			t.endCheck();
		return true;
	}
	
	public Random getRandom() {
		return m_Random;
	}
	
	public void setRandomSeed(long seed) {
		m_Random.setSeed(seed);
	}
	
	public void flipDecisions() {
		while (decideStack.size() > num_solvedatoms) {
			Literal lit = decideStack.remove(decideStack.size() - 1);
			backtrackLiteral(lit);
			// Flip the decision
			lit.getAtom().lastStatus = lit.negate();
		}
		Clause conflict = finalizeBacktrack();
		assert (conflict == null);
		currentDecideLevel = 0;
	}
	
	public void flipNamedLiteral(String name) throws SMTLIBException {
		while (decideStack.size() > num_solvedatoms) {
			Literal lit = decideStack.remove(decideStack.size() - 1);
			backtrackLiteral(lit);
		}
		Clause conflict = finalizeBacktrack();
		assert (conflict == null);
		currentDecideLevel = 0;
		Literal lit = m_assignments.get(name);
		if (lit == null)
			throw new SMTLIBException("Name " + name + " not known");
		DPLLAtom atom = lit.getAtom();
		atom.lastStatus = atom.lastStatus == null ? 
				atom : atom.lastStatus.negate();
	}

	/**
	 * Returns the list of all input clauses. This list does not contain
	 * any learned clauses!
	 */
	public SimpleList<Clause> getClauses() {
		return clauses;
	}
	
	public Term[] getSatisfiedLiterals() {
		int size = 0;
		for (Literal lit : decideStack) {
			if (!(lit.getAtom() instanceof NamedAtom))
				++size;
		}
		Term[] res = new Term[size];
		int i = -1;
		for (Literal lit : decideStack) {
			if (!(lit.getAtom() instanceof NamedAtom))
				res[++i] = lit.getSMTFormula(smtTheory, true);
		}
		return res;
	}
	
	public class AllSatIterator implements Iterator<Term[]> {

		private Literal[] m_Preds;
		private Term[] m_Terms;
		private Literal[] m_Blocker;
		private int m_BlockerSize;
		
		public AllSatIterator(Literal[] preds, Term[] terms) {
			m_Preds = preds;
			m_Terms = terms;
			assert (m_Preds.length == m_Terms.length);
			for (Literal l : preds)
				if (!(l.getAtom() instanceof TrueAtom))
					++m_BlockerSize;
		}
		
		@Override
		public boolean hasNext() {
			if (m_Blocker != null) {
				Clause resolvedBlocker =
						explainConflict(new Clause(m_Blocker, stacklevel));
				learnClause(resolvedBlocker);
			}
			if (solve() && hasModel())
				return true;
			return false;
		}

		@Override
		public Term[] next() {
			Term[] res = new Term[m_Preds.length];
			m_Blocker = new Literal[m_BlockerSize];
			for (int i = 0; i < m_Preds.length; ++i) {
				Literal l = m_Preds[i];
				if (!(l.getAtom() instanceof TrueAtom))
					m_Blocker[i] = l.getAtom().decideStatus.negate();
				res[i] = l.getAtom().decideStatus == l ? 
						m_Terms[i] : getSMTTheory().term("not", m_Terms[i]);
			}
			return res;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException("Cannot remove model!");
		}
		
	}

}
