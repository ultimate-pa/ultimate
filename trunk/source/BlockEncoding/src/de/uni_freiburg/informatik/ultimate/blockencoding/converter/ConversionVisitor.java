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
import de.uni_freiburg.informatik.ultimate.model.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
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

	private HashMap<ProgramPoint, ProgramPoint> origToNewMap;

	private HashMap<String, HashMap<String, ProgramPoint>> locNodesForAnnot;

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
		this.origToNewMap = new HashMap<ProgramPoint, ProgramPoint>();
		this.locNodesForAnnot = new HashMap<String, HashMap<String, ProgramPoint>>();
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
		this.visitedEdges.clear();
		if (startNode == null) {
			s_Logger.warn("Illegal Execution Behaviour,"
					+ "init have to be called, before visitNode()!");
			throw new IllegalStateException(
					"No valid state that startNode == null");
		}
		if (!refNodeMap.containsKey(node)) {
			refNodeMap.put(node, startNode);
		}
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
				// Now we create a converted CodeBlock-edge
				cb = convertMinimizedEdge(edge);
				if (cb instanceof GotoEdge) {
					// it is possible that the found replacement, is Goto-Edge,
					// which we have to convert in a valid edge
					cb = replaceGotoEdge(cb, null);
				}
				s_Logger.debug("<-Converted Formula->: "
						+ cb.getTransitionFormula());
				cb.connectSource(getReferencedNode(edge.getSource()));
				cb.connectTarget(getReferencedNode(edge.getTarget()));
				// now we print out all edges which we added more than two times
				for (IMinimizedEdge key : checkForMultipleFormula.keySet()) {
					if (checkForMultipleFormula.get(key) >= 2) {
						s_Logger.error("Edge: " + key + " Occurence: "
								+ checkForMultipleFormula.get(key));
					}
				}
				// Since we convert function by function, we do not need to
				// follow Call- and Return-Edges
				if (edge.isBasicEdge()
						&& (((IBasicEdge) edge).getOriginalEdge() instanceof Call || ((IBasicEdge) edge)
								.getOriginalEdge() instanceof Return)) {
					continue;
				}
				if (edge.getTarget() != null) {
					internalVisitNode(edge.getTarget());
				}
			}
		}
	}

	/**
	 * We put into our reference map to a minimized node a new ProgramPoint
	 * which is used later on during the conversion, and then we return it. the
	 * access on the map, should always be handled by this method.
	 * 
	 * @param node
	 *            the minimized Node to convert
	 * @return the created ProgramPoint
	 */
	public ProgramPoint getReferencedNode(MinimizedNode node) {
		if (refNodeMap.containsKey(node)) {
			return refNodeMap.get(node);
		} else {
			ASTNode astNode = node.getOriginalNode().getAstNode();
			if (astNode == null
					&& node.getOriginalNode().getPayload().hasLocation()) {
				ILocation loc = node.getOriginalNode().getPayload()
						.getLocation();
				if (loc instanceof BoogieLocation) {
					astNode = ((BoogieLocation) loc).getASTNode();
				}
			}
			ProgramPoint newNode = new ProgramPoint(node.getOriginalNode()
					.getPosition(), node.getOriginalNode().getProcedure(), node
					.getOriginalNode().isErrorLocation(), astNode, null, null);
			refNodeMap.put(node, newNode);
			// to reset the rootAnnot, we need to keep a map from the original
			// program points, to the new ones. And since we only create
			// ProgramPoints here it is the right place to store it.
			origToNewMap.put(node.getOriginalNode(), newNode);
			// In addition we also have to fill the map which stores every
			// ProgramPoint in relation to its name and the procedure name
			if (locNodesForAnnot.containsKey(newNode.getProcedure())) {
				locNodesForAnnot.get(newNode.getProcedure()).put(
						newNode.getLocationName(), newNode);
			} else {
				HashMap<String, ProgramPoint> newMap = new HashMap<String, ProgramPoint>();
				newMap.put(newNode.getLocationName(), newNode);
				locNodesForAnnot.put(newNode.getProcedure(), newMap);
			}
			return newNode;
		}
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
				if (leftSide instanceof GotoEdge
						&& rightSide instanceof GotoEdge) {
					// Special case, we construct an "assume true"
					return replaceGotoEdge(leftSide, rightSide);
				} else if (leftSide instanceof GotoEdge) {
					return rightSide;
				} else if (rightSide instanceof GotoEdge) {
					return leftSide;
				}
				return new SequentialComposition(null, null, boogie2smt,
						leftSide, rightSide);
			}
			if (edge instanceof DisjunctionEdge) {
				if (leftSide instanceof GotoEdge) {
					leftSide = replaceGotoEdge(leftSide, null);
				}
				if (rightSide instanceof GotoEdge) {
					rightSide = replaceGotoEdge(rightSide, null);
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
	 * This method replaces an Goto-Edge with the statement "assume true". <br>
	 * TODO: Need to be clarified if this is correct.
	 * 
	 * @param gotoEdge
	 *            the Goto-Edge to convert
	 * @param secondGotoEdge
	 *            maybe somites we have to convert two Goto-Edges
	 * @return the converted "assume true"
	 */
	private CodeBlock replaceGotoEdge(CodeBlock gotoEdge,
			CodeBlock secondGotoEdge) {
		StatementSequence replacement = null;
		if (secondGotoEdge == null) {
			replacement = new StatementSequence(
					null,
					null, new AssumeStatement(
							gotoEdge.getPayload().getLocation(),
							new BooleanLiteral(gotoEdge.getPayload()
									.getLocation(), true)));
		} else {
			replacement = new StatementSequence(
					null,
					null,
					new AssumeStatement(gotoEdge.getPayload().getLocation(),
							new BooleanLiteral(gotoEdge.getPayload()
									.getLocation(), true)));
		}
		transFormBuilder.addTransitionFormulas(replacement);
		return replacement;
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

	/**
	 * @return the origToNewMap
	 */
	public HashMap<ProgramPoint, ProgramPoint> getOrigToNewMap() {
		return origToNewMap;
	}

	/**
	 * @return the locNodesForAnnot
	 */
	public HashMap<String, HashMap<String, ProgramPoint>> getLocNodesForAnnot() {
		return locNodesForAnnot;
	}
}
