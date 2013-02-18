/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.converter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.visitor.IMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * This special visitor class is responsible for the conversion from
 * MinimizedEdges and MinimizedNodes, back to ProgramPoint and CodeBlock-Edges.
 * 
 * @author Stefan Wissert
 * 
 */
public class ConversionVisitor implements IMinimizationVisitor {

	private static Logger s_Logger;

	private ProgramPoint startNode;

	private HashMap<MinimizedNode, ProgramPoint> refNodeMap;

	private HashSet<IMinimizedEdge> visitedEdges;

	private Boogie2SMT boogie2smt;

	private TransFormulaBuilder transFormBuilder;

	private HashMap<IMinimizedEdge, Integer> checkForMultipleFormula;

	/**
	 * @param boogie2smt
	 * @param root
	 */
	public ConversionVisitor(Boogie2SMT boogie2smt, RootNode root) {
		this.refNodeMap = new HashMap<MinimizedNode, ProgramPoint>();
		this.visitedEdges = new HashSet<IMinimizedEdge>();
		this.boogie2smt = boogie2smt;
		this.checkForMultipleFormula = new HashMap<IMinimizedEdge, Integer>();
		this.transFormBuilder = new TransFormulaBuilder(boogie2smt,
				root.getRootAnnot());
	}

	/**
	 * This method have to be called before the visitNode-Method!
	 * 
	 * @param startNode
	 *            initial start point for the conversion
	 */
	public void init(ProgramPoint startNode) {
		s_Logger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
		this.startNode = startNode;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.interfaces.visitor.
	 * IRCFGVisitor
	 * #visitNode(de.uni_freiburg.informatik.ultimate.blockencoding.model
	 * .MinimizedNode)
	 */
	@Override
	public void visitNode(MinimizedNode node) {
		this.refNodeMap.clear();
		this.visitedEdges.clear();
		if (startNode == null) {
			s_Logger.warn("Illegal Execution Behaviour,"
					+ "init have to be called, before visitNode()!");
			throw new IllegalStateException(
					"No valid state that startNode == null");
		}
		this.refNodeMap.put(node, startNode);
		// Start recursion here
		internalVisitNode(node);
	}

	/**
	 * This method runs recursively over all minimized nodes, which are
	 * reachable from the initial node (function head). While doing this we
	 * convert every edge into a valid CodeBlock and every node in a
	 * ProgramPoint. In the end the whole function is translated in a RCFG.
	 * 
	 * @param node
	 *            MinimizedNode to convert
	 */
	private void internalVisitNode(MinimizedNode node) {
		// We have no outgoing edges, so we reached an end of the recursion
		if (node.getOutgoingEdges() == null
				|| node.getOutgoingEdges().size() == 0) {
			return;
		}

		// next step is to check if we already have mapping to a ProgramPoint
		if (!refNodeMap.containsKey(node)) {
			// if not, we generate one
			initRefMap(node);
		}
		// TODO: First we take here the most minimized variant,
		// later we would choose here the probably best variant (according to
		// SMTSolver)
		ArrayList<IMinimizedEdge> edgeList = new ArrayList<IMinimizedEdge>(
				node.getMinimalOutgoingEdgeLevel());
		for (IMinimizedEdge edge : edgeList) {
			if (!visitedEdges.contains(edge)) {
				visitedEdges.add(edge);
				// the minimized edge here has to be converted to a
				// CodeBlock-Edge
				CodeBlock cb = null;
				checkForMultipleFormula.clear();
				s_Logger.debug("New Converted Edge: " + edge + " Source: "
						+ edge.getSource() + " / Target: " + edge.getTarget());
				s_Logger.debug("Size of Formula: " + edge.getElementCount());
				cb = convertMinimizedEdge(edge);
				s_Logger.debug("<-Converted Formula->: "
						+ cb.getTransitionFormula());
				cb.connectSource(refNodeMap.get(edge.getSource()));
				if (!refNodeMap.containsKey(edge.getTarget())) {
					initRefMap(edge.getTarget());
				}
				cb.connectTarget(refNodeMap.get(edge.getTarget()));
				// now we print out all edges which we added more than two times
				for (IMinimizedEdge key : checkForMultipleFormula.keySet()) {
					if (checkForMultipleFormula.get(key) >= 2) {
						s_Logger.error("Edge: " + key + " Occurence: "
								+ checkForMultipleFormula.get(key));
					}
				}
				if (edge.getTarget() != null) {
					internalVisitNode(edge.getTarget());
				}
			}
		}
	}

	/**
	 * We put into our reference map to a minimized node a new ProgramPoint
	 * which is used later on during the conversion
	 * 
	 * @param node
	 *            the minimized Node to convert
	 */
	private void initRefMap(MinimizedNode node) {
		refNodeMap.put(node, new ProgramPoint(node.getOriginalNode()
				.getPosition(), node.getOriginalNode().getProcedure(), node
				.getOriginalNode().isErrorLocation(), node.getOriginalNode()
				.getAstNode(), null, null));
	}

	/**
	 * This recursive method, converts a MinimizedEdge into a valid CodeBlock.
	 * While doing this, the method uses "Sequential" and "Parallel"
	 * Composition.
	 * 
	 * @param edge
	 *            the minimized edge to convert
	 * @return a converted CodeBlock
	 */
	private CodeBlock convertMinimizedEdge(IMinimizedEdge edge) {
		if (checkForMultipleFormula.containsKey(edge)) {
			checkForMultipleFormula.put(edge,
					((Integer) checkForMultipleFormula.get(edge)) + 1);
		} else {
			checkForMultipleFormula.put(edge, 1);
		}
		// We build a CodeBlock using Recursion
		// We reach one end if we have an BasicEdge
		if (edge.isBasicEdge()) {
			CodeBlock cb = ((IBasicEdge) edge).getOriginalEdge();
			CodeBlock copyOfCodeBlock = null;
			// We need to convert the basic edges, into new ones
			// -> so basically we create a new instance of the CodeBlock,
			// this is necessary to avoid mixing of the models
			if (cb instanceof StatementSequence) {
				copyOfCodeBlock = new StatementSequence(null, null,
						((StatementSequence) cb).getStatements(),
						((StatementSequence) cb).getOrigin());
			}
			if (cb instanceof Call) {
				copyOfCodeBlock = new Call(null, null,
						((Call) cb).getCallStatement(),
						((Call) cb).getOldVarsAssignment(),
						((Call) cb).getGlobalVarsAssignment());
			}
			if (cb instanceof Return) {
				copyOfCodeBlock = new Return(null, null,
						((Return) cb).getCorrespondingCallAnnot(),
						((Return) cb).getCallerNode());
			}
			if (cb instanceof Summary) {
				copyOfCodeBlock = cb;
			}
			if (cb instanceof GotoEdge) {
				copyOfCodeBlock = cb;
			}
			if (copyOfCodeBlock == null) {
				throw new IllegalArgumentException("Failure while converting a"
						+ "CodeBlock, maybe there is a new type,"
						+ "which should be added");
			} else {
				copyOfCodeBlock.setTransitionFormula(cb.getTransitionFormula());
				return copyOfCodeBlock;
			}
		}

		if (edge instanceof ICompositeEdge) {
			IMinimizedEdge[] edges = ((ICompositeEdge) edge)
					.getCompositeEdges();
			CodeBlock leftSide = convertMinimizedEdge(edges[0]);
			CodeBlock rightSide = convertMinimizedEdge(edges[1]);
			if (leftSide == null && rightSide == null) {
				s_Logger.error("Conversion fails, both sides are null ("
						+ edges[0] + " -- " + edges[1] + ")");
				throw new IllegalStateException(
						"Conversion failure, both sides are null");
			}
			// This situation can happen, if a Call/Return/Summary-Edges are
			// involved, they are not part of the formula and are ignored
			if (leftSide instanceof Summary) {
				return rightSide;
			}
			if (rightSide instanceof Summary) {
				return leftSide;
			}
			if (edge instanceof ConjunctionEdge) {
				// In a conjunction, we can ignore GotoEdges
				if (leftSide instanceof GotoEdge) {
					return rightSide;
				} else if (rightSide instanceof GotoEdge) {
					return leftSide;
				}
				return new SequentialComposition(null, null, boogie2smt,
						leftSide, rightSide);
			}
			if (edge instanceof DisjunctionEdge) {
				// In a disjunction, we have to threat GotoEdges
				// we convert them to "assume true" TODO: is that right?
				if (leftSide instanceof GotoEdge) {
					leftSide = new StatementSequence(
							(ProgramPoint) leftSide.getSource(),
							(ProgramPoint) leftSide.getTarget(),
							new AssumeStatement(leftSide.getPayload()
									.getLocation(), new BooleanLiteral(leftSide
									.getPayload().getLocation(), true)));
					transFormBuilder.addTransitionFormulas(leftSide);
				}
				if (rightSide instanceof GotoEdge) {
					rightSide = new StatementSequence(
							(ProgramPoint) rightSide.getSource(),
							(ProgramPoint) rightSide.getTarget(),
							new AssumeStatement(rightSide.getPayload()
									.getLocation(), new BooleanLiteral(
									rightSide.getPayload().getLocation(), true)));
					transFormBuilder.addTransitionFormulas(rightSide);
				}
				return new ParallelComposition(null, null, boogie2smt,
						leftSide, rightSide);
			}
		}
		// should never reach this end here?
		s_Logger.error("Failure during construction of formulas... " + edge);
		return null;
	}

	/**
	 * TODO: This method exist only for debugging, can be deleted when not
	 * needed anymore
	 * 
	 * @param edge
	 * @return
	 */
	@SuppressWarnings("unused")
	private void fakeConvertMinimizedEdge(IMinimizedEdge edge) {
		if (checkForMultipleFormula.containsKey(edge)) {
			checkForMultipleFormula.put(edge,
					((Integer) checkForMultipleFormula.get(edge)) + 1);
		} else {
			checkForMultipleFormula.put(edge, 1);
		}
		// We build a CodeBlock using Recursion
		// We reach one end if we have an BasicEdge
		if (edge.isBasicEdge()) {
			return;
		}

		if (edge instanceof ICompositeEdge) {
			IMinimizedEdge[] edges = ((ICompositeEdge) edge)
					.getCompositeEdges();
			fakeConvertMinimizedEdge(edges[0]);
			fakeConvertMinimizedEdge(edges[1]);
			return;
		}
		// should never reach this end here?
		s_Logger.error("Failure during construction of formulas... " + edge);
		return;
	}
}
