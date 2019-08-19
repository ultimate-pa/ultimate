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
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadOther;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.JoinThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.JoinThreadOther;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class RCFGBacktranslator extends
		DefaultTranslator<IIcfgTransition<IcfgLocation>, BoogieASTNode, Term, Expression, IcfgLocation, String> {

	private final ILogger mLogger;
	private Term2Expression mTerm2Expression;

	/**
	 * Mapping from auxiliary CodeBlocks to source BoogieAstNodes. For assert, the requires assumed at begin of
	 * procedure, and ensures the result is a singleton. For the assert requires before the call the result contains two
	 * elements: First, the call, afterwards the requires.
	 */
	private final Map<Statement, BoogieASTNode[]> mCodeBlock2Statement = new HashMap<>();

	public RCFGBacktranslator(final ILogger logger) {
		super(IcfgEdge.class, BoogieASTNode.class, Term.class, Expression.class);
		mLogger = logger;
	}

	/**
	 * @param term2Expression
	 *            the term2Expression to set
	 */
	public void setTerm2Expression(final Term2Expression term2Expression) {
		mTerm2Expression = term2Expression;
	}

	public BoogieASTNode[] putAux(final Statement aux, final BoogieASTNode[] source) {
		return mCodeBlock2Statement.put(aux, source);
	}

	@Override
	public List<BoogieASTNode> translateTrace(final List<IIcfgTransition<IcfgLocation>> trace) {
		final List<IIcfgTransition<IcfgLocation>> cbTrace = trace;
		final List<AtomicTraceElement<BoogieASTNode>> atomicTeList = new ArrayList<>();
		for (final IIcfgTransition<IcfgLocation> elem : cbTrace) {
			if (!(elem instanceof CodeBlock)) {
				throw new AssertionError("unknown rcfg element");
			}
			addCodeBlock(elem, null, null, null, atomicTeList, null);
		}
		final List<BoogieASTNode> result = new ArrayList<>();
		for (final AtomicTraceElement<BoogieASTNode> ate : atomicTeList) {
			result.add(ate.getTraceElement());
		}
		return result;
	}

	private void addCodeBlock(final AtomicTraceElement<IIcfgTransition<IcfgLocation>> ate,
			final List<AtomicTraceElement<BoogieASTNode>> trace, final Map<TermVariable, Boolean> branchEncoders) {
		final IIcfgTransition<IcfgLocation> cb = ate.getTraceElement();
		final IRelevanceInformation relevanceInformation = ate.getRelevanceInformation();
		addCodeBlock(cb, relevanceInformation, ate.hasThreadId() ? ate.getThreadId() : null,
				ate.getStepInfo().contains(StepInfo.FORK) ? ate.getForkedThreadId() : null, trace, branchEncoders);
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
	private void addCodeBlock(final IIcfgTransition<IcfgLocation> cb, final IRelevanceInformation relevanceInformation,
			final Integer threadId, final Integer forkedThreadId, final List<AtomicTraceElement<BoogieASTNode>> trace,
			final Map<TermVariable, Boolean> branchEncoders) {

		final AtomicTraceElementBuilder<BoogieASTNode> ateBuilder = new AtomicTraceElementBuilder<>();
		ateBuilder.setRelevanceInformation(relevanceInformation);
		ateBuilder.setToStringFunc(BoogiePrettyPrinter.getBoogieToStringProvider());
		if (threadId != null) {
			ateBuilder.setThreadId(threadId);
		}
		if (forkedThreadId != null) {
			ateBuilder.setForkedThreadId(forkedThreadId);
		}
		ateBuilder.setProcedures(cb.getPrecedingProcedure(), cb.getSucceedingProcedure());
		if (cb instanceof Call) {
			final Statement st = ((Call) cb).getCallStatement();
			ateBuilder.setStepAndElement(st);
			ateBuilder.setStepInfo(StepInfo.PROC_CALL);
		} else if (cb instanceof Return) {
			final Statement st = ((Return) cb).getCallStatement();
			ateBuilder.setStepAndElement(st);
			ateBuilder.setStepInfo(StepInfo.PROC_RETURN);
		} else if (cb instanceof ForkThreadOther) {
			final Statement st = ((ForkThreadOther) cb).getForkStatement();
			ateBuilder.setStepAndElement(st);
			ateBuilder.setStepInfo(StepInfo.FORK);
		} else if (cb instanceof ForkThreadCurrent) {
			final Statement st = ((ForkThreadCurrent) cb).getForkStatement();
			ateBuilder.setStepAndElement(st);
			ateBuilder.setStepInfo(StepInfo.FORK);
		} else if (cb instanceof JoinThreadOther) {
			final Statement st = ((JoinThreadOther) cb).getJoinStatement();
			ateBuilder.setStepAndElement(st);
			ateBuilder.setStepInfo(StepInfo.JOIN);
		} else if (cb instanceof JoinThreadCurrent) {
			final Statement st = ((JoinThreadCurrent) cb).getJoinStatement();
			ateBuilder.setStepAndElement(st);
			ateBuilder.setStepInfo(StepInfo.JOIN);
		} else if (cb instanceof Summary) {
			final Statement st = ((Summary) cb).getCallStatement();
			// FIXME: Is summary call, return or something new?
			ateBuilder.setStepAndElement(st);
		} else if (cb instanceof StatementSequence) {
			final StatementSequence ss = (StatementSequence) cb;
			for (final Statement st : ss.getStatements()) {
				final BoogieASTNode[] sources = mCodeBlock2Statement.get(st);
				if (sources != null) {
					for (final BoogieASTNode source : sources) {
						ateBuilder.setStepAndElement(source);
						trace.add(ateBuilder.build());
					}

				} else {
					ateBuilder.setStepAndElement(st);
					trace.add(ateBuilder.build());
				}
			}
			return;
		} else if (cb instanceof SequentialComposition) {
			final SequentialComposition seqComp = (SequentialComposition) cb;
			for (final CodeBlock sccb : seqComp.getCodeBlocks()) {
				addCodeBlock(sccb, relevanceInformation, threadId, forkedThreadId, trace, branchEncoders);
			}
			return;
		} else if (cb instanceof ParallelComposition) {
			final ParallelComposition parComp = (ParallelComposition) cb;
			final Map<TermVariable, CodeBlock> bi2cb = parComp.getBranchIndicator2CodeBlock();
			if (branchEncoders == null) {
				final CodeBlock someBranch = bi2cb.entrySet().iterator().next().getValue();
				addCodeBlock(someBranch, relevanceInformation, threadId, forkedThreadId, trace, branchEncoders);
				final ILocation loc = ILocation.getAnnotation(cb.getSource());
				mLogger.warn("You are using large block encoding together with an algorithm for which the "
						+ "backtranslation into program statements is not yet implemented.");
				if (loc == null) {
					mLogger.error("unable to determine which branch was taken, unable to determine the location");
				} else {
					mLogger.warn("unable to determine which branch was taken at " + loc);
				}
				return;
			}
			for (final Entry<TermVariable, CodeBlock> entry : bi2cb.entrySet()) {
				final boolean taken = branchEncoders.get(entry.getKey());
				if (taken) {
					addCodeBlock(entry.getValue(), relevanceInformation, threadId, forkedThreadId, trace,
							branchEncoders);
					return;
				}
			}
			throw new AssertionError("no branch was taken");
		} else if (cb instanceof GotoEdge) {
			// skip goto edges
			return;
		} else {
			throw new UnsupportedOperationException("Unsupported CodeBlock: " + cb.getClass().getCanonicalName());
		}
		trace.add(ateBuilder.build());
	}

	@Override
	public IProgramExecution<BoogieASTNode, Expression>

			translateProgramExecution(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> programExecution) {
		if (!(programExecution instanceof IcfgProgramExecution)) {
			throw new IllegalArgumentException();
		}
		final IcfgProgramExecution rcfgProgramExecution = (IcfgProgramExecution) programExecution;
		assert checkCallStackSourceProgramExecution(mLogger,
				programExecution) : "callstack of initial program execution already broken";

		final List<AtomicTraceElement<BoogieASTNode>> trace = new ArrayList<>();
		final Map<Integer, ProgramState<Expression>> programStateMapping = new HashMap<>();

		if (rcfgProgramExecution.getInitialProgramState() != null) {
			programStateMapping.put(-1, translateProgramState(rcfgProgramExecution.getInitialProgramState()));
		}
		for (int i = 0; i < rcfgProgramExecution.getLength(); i++) {
			final AtomicTraceElement<IIcfgTransition<IcfgLocation>> ate = rcfgProgramExecution.getTraceElement(i);
			final Map<TermVariable, Boolean>[] branchEncoders = rcfgProgramExecution.getBranchEncoders();
			if (branchEncoders == null || i >= branchEncoders.length) {
				addCodeBlock(ate, trace, null);
			} else {
				addCodeBlock(ate, trace, branchEncoders[i]);
			}
			final int posInNewTrace = trace.size() - 1;
			final ProgramState<Term> programState = rcfgProgramExecution.getProgramState(i);
			programStateMapping.put(posInNewTrace, translateProgramState(programState));
		}
		assert checkCallStackTarget(mLogger, trace);
		return new BoogieProgramExecution(programStateMapping, trace, programExecution.isConcurrent());
	}

	@Override
	public IBacktranslatedCFG<String, BoogieASTNode>
			translateCFG(final IBacktranslatedCFG<IcfgLocation, IIcfgTransition<IcfgLocation>> cfg) {
		final IBacktranslatedCFG<String, BoogieASTNode> translatedCfg =
				translateCFG(cfg, (a, b, c) -> translateCFGEdge(a, (IIcfgTransition<IcfgLocation>) b, c));
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
			final Map<IExplicitEdgesMultigraph<?, ?, IcfgLocation, ? extends IIcfgTransition<IcfgLocation>, ?>, Multigraph<String, BoogieASTNode>> cache,
			final IIcfgTransition<IcfgLocation> oldEdge, final Multigraph<String, BoogieASTNode> newSourceNode) {
		final IcfgLocation oldTarget = oldEdge.getTarget();
		final IExplicitEdgesMultigraph<IcfgLocation, IcfgEdge, IcfgLocation, ? extends IIcfgTransition<IcfgLocation>, VisualizationNode> bla =
				oldTarget;
		// this is the node we want to return
		Multigraph<String, BoogieASTNode> newTarget;
		if (oldTarget != null) {
			newTarget = cache.get(oldTarget);
			if (newTarget == null) {
				newTarget = createWitnessNode(oldTarget);
				cache.put(oldTarget, newTarget);
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
		} else {
			// we assume that all other edges are "virtual" edges (i.e., root edges).
			// a root edge is either a goto or null, i.e., we separate the rcfg
			final BoogieIcfgLocation pp = (BoogieIcfgLocation) oldEdge.getTarget();
			if (!pp.getProcedure().equals("ULTIMATE.start")) {
				mLogger.info("Ignoring RootEdge to procedure " + pp.getProcedure());
				return null;
			}
			createNewEdge(newSourceNode, newTarget, null);
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

	private static void createNewEdge(final Multigraph<String, BoogieASTNode> source,
			final Multigraph<String, BoogieASTNode> target, final BoogieASTNode label) {
		new MultigraphEdge<>(source, label, target);
	}

	private static Multigraph<String, BoogieASTNode> createWitnessNode(final IcfgLocation old) {
		final WitnessInvariant inv = WitnessInvariant.getAnnotation(old);
		final Multigraph<String, BoogieASTNode> rtr = new Multigraph<>(inv == null ? null : inv.getInvariant());
		ModelUtils.copyAnnotations(old, rtr);
		return rtr;
	}

	@Override
	public Expression translateExpression(final Term term) {
		return mTerm2Expression.translate(term);
	}

}
