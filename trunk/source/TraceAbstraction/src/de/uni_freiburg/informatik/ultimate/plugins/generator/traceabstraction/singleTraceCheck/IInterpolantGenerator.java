package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Interface for objects that generate sequences of interpolants.
 * Given
 * <ul>
 * <li>a precondition stated by predicate φ_0
 * <li>a postcondition stated by predicate φ_n
 * <li>a trace (which is a word of CodeBlocks) cb_0 cb_1 ... cb_{n-1},
 * </ul>
 * a sequence of interpolants is a sequence of predicates φ_1,...,φ_{n-1} 
 * such that the inclusion post(φ_i, cb_i}) ⊆ φ_{i+1} holds for 0⩽i<n.
 * 
 * A sequence of interpolants can be seen as a Hoare annotation for the program
 * that corresponds to the trace.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public interface IInterpolantGenerator {

	public abstract Word<CodeBlock> getTrace();

	public abstract IPredicate getPrecondition();

	public abstract IPredicate getPostcondition();

	public abstract Map<Integer, IPredicate> getPendingContexts();

	public abstract IPredicate[] getInterpolants();

}