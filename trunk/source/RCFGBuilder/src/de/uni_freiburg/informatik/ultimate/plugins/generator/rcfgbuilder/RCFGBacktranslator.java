/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.Multigraph;
import de.uni_freiburg.informatik.ultimate.core.lib.models.MultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IToString;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;

public class RCFGBacktranslator extends DefaultTranslator<RCFGEdge, BoogieASTNode, Term, Expression> {

	private final ILogger mLogger;
	private Term2Expression mTerm2Expression;

	public RCFGBacktranslator(final ILogger logger) {
		super(RCFGEdge.class, BoogieASTNode.class, Term.class, Expression.class);
		mLogger = logger;
	}
	
	

	/**
	 * @param term2Expression the term2Expression to set
	 */
	public void setTerm2Expression(final Term2Expression term2Expression) {
		mTerm2Expression = term2Expression;
	}



	/**
	 * Mapping from auxiliary CodeBlocks to source BoogieAstNodes. For assert, the requires assumed at begin of
	 * procedure, and ensures the result is a singleton. For the assert requires before the call the result contains two
	 * elements: First, the call, afterwards the requires.
	 */
	private final Map<Statement, BoogieASTNode[]> mCodeBlock2Statement = new HashMap<Statement, BoogieASTNode[]>();

	public BoogieASTNode[] putAux(final Statement aux, final BoogieASTNode[] source) {
		return mCodeBlock2Statement.put(aux, source);
	}

	@Override
	public List<BoogieASTNode> translateTrace(final List<RCFGEdge> trace) {
		final List<RCFGEdge> cbTrace = trace;
		final List<AtomicTraceElement<BoogieASTNode>> atomicTeList = new ArrayList<AtomicTraceElement<BoogieASTNode>>();
		for (final RcfgElement elem : cbTrace) {
			if (elem instanceof CodeBlock) {
				addCodeBlock((CodeBlock) elem, atomicTeList, null, null);
			} else if (elem instanceof ProgramPoint) {

			} else {
				throw new AssertionError("unknown rcfg element");
			}
		}
		final List<BoogieASTNode> result = new ArrayList<BoogieASTNode>();
		for (final AtomicTraceElement<BoogieASTNode> ate : atomicTeList) {
			result.add(ate.getTraceElement());
		}
		return result;
	}

	/**
	 * Transform a single (possibly large) CodeBlock to a list of BoogieASTNodes and add these BoogieASTNodes to the
	 * List trace. If
	 * <ul>
	 * <li>if the CodeBlock contains a single Statement we add this statement
	 * <li>if the CodeBlock is a StatementsSequence we translate all Statements back to their original BoogieASTNodes
	 * (e.g., assume Statements might be translated to assert Statements, assume Statements might be translated to
	 * requires/ensures specifications)
	 * <li>if the CodeBlock is a SequentialComposition we call this method recursively
	 * <li>if the CodeBlock is a ParallelComposition we ask the branchEncoders mapping on which branch we call this
	 * method recursively. If the branchEncoders mapping is null (occurs e.g., for traces whose feasibility can not be
	 * determined) we call this method recursively on some branch.
	 * </ul>
	 */
	private void addCodeBlock(final RCFGEdge cb, final List<AtomicTraceElement<BoogieASTNode>> trace,
			final Map<TermVariable, Boolean> branchEncoders, final IRelevanceInformation relevanceInformation) {
		final IToString<BoogieASTNode> stringProvider = BoogiePrettyPrinter.getBoogieToStringprovider();
		if (cb instanceof Call) {
			final Statement st = ((Call) cb).getCallStatement();
			trace.add(new AtomicTraceElement<BoogieASTNode>(st, st, StepInfo.PROC_CALL, stringProvider,
					relevanceInformation));
		} else if (cb instanceof Return) {
			final Statement st = ((Return) cb).getCallStatement();
			trace.add(new AtomicTraceElement<BoogieASTNode>(st, st, StepInfo.PROC_RETURN, stringProvider,
					relevanceInformation));
		} else if (cb instanceof Summary) {
			final Statement st = ((Summary) cb).getCallStatement();
			// FIXME: Is summary call, return or something new?
			trace.add(
					new AtomicTraceElement<BoogieASTNode>(st, st, StepInfo.NONE, stringProvider, relevanceInformation));
		} else if (cb instanceof StatementSequence) {
			final StatementSequence ss = (StatementSequence) cb;
			for (final Statement statement : ss.getStatements()) {
				if (mCodeBlock2Statement.containsKey(statement)) {
					final BoogieASTNode[] sources = mCodeBlock2Statement.get(statement);
					for (final BoogieASTNode source : sources) {
						trace.add(new AtomicTraceElement<BoogieASTNode>(source, stringProvider, relevanceInformation));
					}
				} else {
					trace.add(new AtomicTraceElement<BoogieASTNode>(statement, stringProvider, relevanceInformation));
				}
			}
		} else if (cb instanceof SequentialComposition) {
			final SequentialComposition seqComp = (SequentialComposition) cb;
			for (final CodeBlock sccb : seqComp.getCodeBlocks()) {
				addCodeBlock(sccb, trace, branchEncoders, relevanceInformation);
			}
		} else if (cb instanceof ParallelComposition) {
			final ParallelComposition parComp = (ParallelComposition) cb;
			final Map<TermVariable, CodeBlock> bi2cb = parComp.getBranchIndicator2CodeBlock();
			if (branchEncoders == null) {
				final CodeBlock someBranch = bi2cb.entrySet().iterator().next().getValue();
				addCodeBlock(someBranch, trace, branchEncoders, relevanceInformation);
			} else {
				for (final Entry<TermVariable, CodeBlock> entry : bi2cb.entrySet()) {
					final boolean taken = branchEncoders.get(entry.getKey());
					if (taken) {
						addCodeBlock(entry.getValue(), trace, branchEncoders, relevanceInformation);
						return;
					}
				}
			}
			throw new AssertionError("no branch was taken");
		} else if (cb instanceof GotoEdge) {
			return;
		} else {
			throw new UnsupportedOperationException("Unsupported CodeBlock" + cb.getClass().getCanonicalName());
		}
	}

	@Override
	public IProgramExecution<BoogieASTNode, Expression>
			translateProgramExecution(final IProgramExecution<RCFGEdge, Term> programExecution) {
		if (!(programExecution instanceof RcfgProgramExecution)) {
			throw new IllegalArgumentException();
		}
		final RcfgProgramExecution rcfgProgramExecution = (RcfgProgramExecution) programExecution;

		final List<AtomicTraceElement<BoogieASTNode>> trace = new ArrayList<AtomicTraceElement<BoogieASTNode>>();
		final Map<Integer, ProgramState<Expression>> programStateMapping =
				new HashMap<Integer, ProgramState<Expression>>();

		if (rcfgProgramExecution.getInitialProgramState() != null) {
			programStateMapping.put(-1, translateProgramState(rcfgProgramExecution.getInitialProgramState()));
		}
		for (int i = 0; i < rcfgProgramExecution.getLength(); i++) {
			final AtomicTraceElement<RCFGEdge> codeBlock = rcfgProgramExecution.getTraceElement(i);
			final Map<TermVariable, Boolean>[] branchEncoders = rcfgProgramExecution.getBranchEncoders();
			if (branchEncoders == null || i >= branchEncoders.length) {
				addCodeBlock(codeBlock.getTraceElement(), trace, null, codeBlock.getRelevanceInformation());
			} else {
				addCodeBlock(codeBlock.getTraceElement(), trace, branchEncoders[i],
						codeBlock.getRelevanceInformation());
			}
			final int posInNewTrace = trace.size() - 1;
			final ProgramState<Term> programState = rcfgProgramExecution.getProgramState(i);
			programStateMapping.put(posInNewTrace, translateProgramState(programState));
		}
		return new BoogieProgramExecution(programStateMapping, trace);
	}

	@Override
	public IBacktranslatedCFG<String, BoogieASTNode> translateCFG(final IBacktranslatedCFG<?, RCFGEdge> cfg) {
		if (!(cfg.getCFGs().stream().allMatch(a -> a instanceof RootNode))) {
			throw new UnsupportedOperationException("Cannot translate cfg that is not an RCFG");
		}
		final IBacktranslatedCFG<String, BoogieASTNode> translatedCfg =
				translateCFG(cfg, (a, b, c) -> translateCFGEdge(a, (RCFGEdge) b, c));
		// mLogger.info(getClass().getSimpleName());
		// printHondas(cfg, mLogger::info);
		// printCFG(cfg, mLogger::info);
		// mLogger.info("######## END "+getClass().getSimpleName());
		return translatedCfg;
	}

	/**
	 * Translate a given edge, attach the result of the translation (possibly a graph) to newsourcenode and return a
	 * targetnode that can be used to continue the translation.
	 *
	 * @param cache
	 */
	@SuppressWarnings("unchecked")
	private <TVL> Multigraph<String, BoogieASTNode> translateCFGEdge(
			final Map<IExplicitEdgesMultigraph<?, ?, TVL, RCFGEdge, ?>, Multigraph<String, BoogieASTNode>> cache,
			final RCFGEdge oldEdge, final Multigraph<String, BoogieASTNode> newSourceNode) {
		final RCFGNode oldTarget = oldEdge.getTarget();
		// this is the node we want to return
		Multigraph<String, BoogieASTNode> newTarget;
		if (oldTarget != null) {
			newTarget = cache.get(oldTarget);
			if (newTarget == null) {
				newTarget = createWitnessNode(oldTarget);
				cache.put((IExplicitEdgesMultigraph<?, ?, TVL, RCFGEdge, ?>) oldTarget, newTarget);
			}
		} else {
			// if the codeblock is disconnected, we need to create some fresh target node
			newTarget = createUnlabeledWitnessNode(null);
		}

		if (oldEdge instanceof Call) {
			final Statement st = ((Call) oldEdge).getCallStatement();
			createNewEdge(newSourceNode, newTarget, st);
		} else if (oldEdge instanceof Return) {
			final Statement st = ((Return) oldEdge).getCallStatement();
			createNewEdge(newSourceNode, newTarget, st);
		} else if (oldEdge instanceof Summary) {
			final Statement st = ((Summary) oldEdge).getCallStatement();
			createNewEdge(newSourceNode, newTarget, st);
		} else if (oldEdge instanceof StatementSequence) {
			final StatementSequence ss = (StatementSequence) oldEdge;
			translateEdgeStatementSequence(newSourceNode, newTarget, ss);
		} else if (oldEdge instanceof SequentialComposition) {
			final SequentialComposition seqComp = (SequentialComposition) oldEdge;
			Multigraph<String, BoogieASTNode> current = newSourceNode;
			for (final CodeBlock sccb : seqComp.getCodeBlocks()) {
				current = translateCFGEdge(cache, sccb, current);
			}
			createNewEdge(current, newTarget, null);
		} else if (oldEdge instanceof ParallelComposition) {
			final ParallelComposition parComp = (ParallelComposition) oldEdge;
			final Map<TermVariable, CodeBlock> bi2cb = parComp.getBranchIndicator2CodeBlock();
			final Iterator<Entry<TermVariable, CodeBlock>> iter = bi2cb.entrySet().iterator();
			while (iter.hasNext()) {
				final CodeBlock someBranch = iter.next().getValue();
				final Multigraph<String, BoogieASTNode> intermediate =
						translateCFGEdge(cache, someBranch, newSourceNode);
				createNewEdge(intermediate, newTarget, null);
			}
		} else if (oldEdge instanceof GotoEdge) {
			// we represent goto with an edge without label
			createNewEdge(newSourceNode, newTarget, null);
		} else if (oldEdge instanceof RootEdge) {
			// a root edge is either a goto or null, i.e., we separate the rcfg
			final ProgramPoint pp = (ProgramPoint) oldEdge.getTarget();
			if (!pp.getProcedure().equals("ULTIMATE.start")) {
				mLogger.info("Ignoring RootEdge to procedure " + pp.getProcedure());
				return null;
			}
			createNewEdge(newSourceNode, newTarget, null);
		} else {
			throw new UnsupportedOperationException("Unsupported CodeBlock" + oldEdge.getClass().getCanonicalName());
		}
		return newTarget;
	}

	private void translateEdgeStatementSequence(final Multigraph<String, BoogieASTNode> newSourceNode,
			final Multigraph<String, BoogieASTNode> newTarget, final StatementSequence ss) {
		int i = 0;
		final int maxIdx = ss.getStatements().size() - 1;
		Multigraph<String, BoogieASTNode> last;
		Multigraph<String, BoogieASTNode> current = newSourceNode;
		for (final Statement statement : ss.getStatements()) {
			last = current;
			if (i == maxIdx) {
				current = newTarget;
			} else {
				current = createUnlabeledWitnessNode(null);
			}
			createNewEdge(last, current, statement);
			++i;
		}
	}

	private void createNewEdge(final Multigraph<String, BoogieASTNode> source,
			final Multigraph<String, BoogieASTNode> target, final BoogieASTNode label) {
		new MultigraphEdge<>(source, label, target);
	}

	private Multigraph<String, BoogieASTNode> createWitnessNode(final RCFGNode old) {
		final WitnessInvariant inv = WitnessInvariant.getAnnotation(old);
		final Multigraph<String, BoogieASTNode> rtr =
				new Multigraph<String, BoogieASTNode>(inv == null ? null : inv.getInvariant());
		ModelUtils.copyAnnotations(old, rtr);
		return rtr;
	}
	
	private ProgramState<Expression> translateProgramState(final ProgramState<Term> oldProgramState) {
		if (oldProgramState == null) {
			return null;
		}
		final Map<Expression, Collection<Expression>> variable2Values = new HashMap<>();
		for (final Term oldVariable : oldProgramState.getVariables()) {
			final Collection<Expression> newValues = new ArrayList<>(); 
			for (final Term oldValue : oldProgramState.getValues(oldVariable)) {
				newValues.add(mTerm2Expression.translate(oldValue));
			}
			final Expression newVariable = mTerm2Expression.translate(oldVariable);
			variable2Values.put(newVariable, newValues);
		}
		return new ProgramState<>(variable2Values );
	}

	@Override
	public Expression translateExpression(final Term term) {
		return mTerm2Expression.translate(term);
	}
	
	
}
