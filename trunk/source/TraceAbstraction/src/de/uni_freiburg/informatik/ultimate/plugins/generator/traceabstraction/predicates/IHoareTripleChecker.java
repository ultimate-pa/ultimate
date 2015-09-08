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

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.ILockHolderWithVoluntaryLockRelease;

/**
 * Object that implement this interface check if Hoare Triples are valid.
 * Hoare triples that we check are of the form
 * { P } cb { Q }
 * where P and Q are given by IPredicates, cb has to be a single CodeBlock.
 * Note that for return statements we have to check a quadruple                                                              
 * @author Matthias Heizmann
 *
 */
public interface IHoareTripleChecker extends ILockHolderWithVoluntaryLockRelease {
	
	/**
	 * Hoare Triple Truth Value. This is the result of a Hoare triple check.
	 */
	public enum Validity { VALID, INVALID, UNKNOWN, NOT_CHECKED };
	
	
	/**
	 * Check if the Hoare triple 
	 *     {pre} cb {succ}
	 * is valid for an internal transition cb. Internal transition means that
	 * the program is in the same procedure before and after the CodeBlock cb
	 * was executed.
	 */
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ);
	
	/**
	 * Check if the Hoare triple 
	 *     {pre} call {succ}
	 * is valid for a call transition. Here, the CodeBlock has to be a call 
	 * statement.
	 */
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ);
	
	/**
	 * Check if the Hoare quadruple 
	 *     {preLin} {preHier} return {succ}
	 * is valid for a return transition. Here, the CodeBlock has to be a return,
	 * preLin is the IPredicate that describes a set of states of the called
	 * procedure before the return, preHier is the IPredicate that describes
	 * a set of states of the calling procedure before the call, and succ
	 * is the IPredicate that describes a set of states of the called procedure.
	 */
	public Validity checkReturn(IPredicate preLin, IPredicate preHier, CodeBlock cb, IPredicate succ);
	
	
	public abstract HoareTripleCheckerBenchmarkGenerator getEdgeCheckerBenchmark(); 

}
