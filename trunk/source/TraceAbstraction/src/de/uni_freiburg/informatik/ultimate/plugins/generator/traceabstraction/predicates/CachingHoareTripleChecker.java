/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap4;

/**
 * IHoareTripleChecker that caches already computed results.
 * Also tries to use these results for more intelligent checks.
 * @author Matthias Heizmann
 *
 */
public class CachingHoareTripleChecker implements IHoareTripleChecker {
	
	private final IHoareTripleChecker m_ComputingHoareTripleChecker;
	private final PredicateUnifier m_PredicateUnifer;
	private final NestedMap3<IPredicate, CodeBlock, IPredicate, Validity> m_InternalCache =
			new NestedMap3<>();
	private final NestedMap3<IPredicate, CodeBlock, IPredicate, Validity> m_CallCache =
			new NestedMap3<>();
	private final NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, Validity> m_ReturnCache =
			new NestedMap4<>();
	private final boolean m_UnknownIfSomeExtendedCacheCheckIsUnknown = true;
	
	public CachingHoareTripleChecker(
			IHoareTripleChecker protectedHoareTripleChecker,
			PredicateUnifier predicateUnifer) {
		super();
		m_ComputingHoareTripleChecker = protectedHoareTripleChecker;
		m_PredicateUnifer = predicateUnifer;
	}

	@Override
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		Validity result = m_InternalCache.get(pre, cb, succ);
		if (result == null) {
			result = extendedCacheCheckInternal(pre,cb,succ);
			if (result == null) {
				result = m_ComputingHoareTripleChecker.checkInternal(pre, cb, succ);
			}
			m_InternalCache.put(pre, cb, succ, result);
		}
		return result;
	}

	private Validity extendedCacheCheckInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		boolean someResultWasUnknown = false;
		{
			Set<IPredicate> strongerThanPre = m_PredicateUnifer.getCoverageRelation().getCoveredPredicates(succ);
			Set<IPredicate> weakerThanSucc = m_PredicateUnifer.getCoverageRelation().getCoveringPredicates(pre);
			for (IPredicate strengthenedPre : strongerThanPre) {
				for (IPredicate weakenedSucc : weakerThanSucc) {
					Validity result = m_InternalCache.get(strengthenedPre, cb, weakenedSucc);
					if (result != null) {
						switch (result) {
						case VALID:
							break;
						case UNKNOWN:
							someResultWasUnknown = true;
							break;
						case INVALID:
							return result;
						case NOT_CHECKED:
							break;
//						throw new IllegalStateException("use protective Hoare triple checker");
						default:
							throw new AssertionError("unknown case");
						}
					}
				}
			}
		}
		{
			Set<IPredicate> weakerThanPre = m_PredicateUnifer.getCoverageRelation().getCoveringPredicates(pre);
			Set<IPredicate> strongerThanSucc = m_PredicateUnifer.getCoverageRelation().getCoveredPredicates(succ);
			for (IPredicate weakenedPre : weakerThanPre) {
				for (IPredicate strengthenedSucc : strongerThanSucc) {
					Validity result = m_InternalCache.get(weakenedPre, cb, strengthenedSucc);
					if (result != null) {
						switch (result) {
						case VALID:
							return result;
						case UNKNOWN:
							someResultWasUnknown = true;
							break;
						case INVALID:
							break;
						case NOT_CHECKED:
							break;
//						throw new IllegalStateException("use protective Hoare triple checker");
						default:
							throw new AssertionError("unknown case");
						}
					}
				}
			}
		}
		if (m_UnknownIfSomeExtendedCacheCheckIsUnknown && someResultWasUnknown) {
			return Validity.UNKNOWN;
		} else {
			return null;
		}
	}

	@Override
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		return m_ComputingHoareTripleChecker.checkCall(pre, cb, succ);
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			CodeBlock cb, IPredicate succ) {
		return m_ComputingHoareTripleChecker.checkReturn(preLin, preHier, cb, succ);
	}
	
	

	@Override
	public HoareTripleCheckerBenchmarkGenerator getEdgeCheckerBenchmark() {
		return m_ComputingHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	public IHoareTripleChecker getProtectedHoareTripleChecker() {
		return m_ComputingHoareTripleChecker;
	}

	@Override
	public void releaseLock() {
		m_ComputingHoareTripleChecker.releaseLock();
	}
	
	

}
