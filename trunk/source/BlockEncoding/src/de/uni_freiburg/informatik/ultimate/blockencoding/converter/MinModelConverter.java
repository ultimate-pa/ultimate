/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.converter;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.BlockEncodingAnnotation;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * This class is like BlockEncoder, the start point where every function in the
 * program is converted back to an RCFG. An advantage is, that this can be
 * executed in parallel, which gives some performance gains.
 * 
 * @author Stefan Wissert
 * 
 */
public class MinModelConverter {

	/**
	 * Shared Ultimate Logger instance.
	 */
	private static Logger s_Logger;

	private Boogie2SMT boogie2smt;

	private ConversionVisitor convertVisitor;

	/**
	 * Public Constructor.
	 */
	public MinModelConverter() {
		s_Logger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
	}

	/**
	 * Starting point of the back conversion to an RCFG. Note: Due to changes of
	 * data model, the minimized model belongs now as Annotation at the
	 * RootEdges.
	 * 
	 * @param root
	 *            the rootNode to convert
	 * @return the converted rootNode
	 */
	public RootNode startConversion(RootNode root) {
		RootNode newRoot = new RootNode(root.getRootAnnot());
		boogie2smt = new Boogie2SMT(newRoot.getRootAnnot().getScript(), false,
				false);
		convertVisitor = new ConversionVisitor(boogie2smt, root);
		for (RCFGEdge edge : root.getOutgoingEdges()) {
			if (edge instanceof RootEdge) {
				BlockEncodingAnnotation annot = BlockEncodingAnnotation
						.getAnnotation(edge);
				if (annot != null) {
					new RootEdge(newRoot, convertFunction(annot.getNode()));
				} else {
					s_Logger.warn("Conversion cancelled, illegal RCFG!");
					throw new IllegalArgumentException(
							"The target of an root edge is not a MinimizedNode");
				}
			} else {
				s_Logger.warn("Conversion cancelled, illegal RCFG!");
				throw new IllegalArgumentException(
						"An outgoing edge of RootNode is not a RootEdge");
			}
		}
		return newRoot;
	}

	/**
	 * Converts a function (given as MinimizedNode) by calling the
	 * ConversionVisitor.
	 * 
	 * @param node
	 *            function head
	 * @return converted ProgramPoint
	 */
	private ProgramPoint convertFunction(MinimizedNode node) {
		ProgramPoint newNode = new ProgramPoint(node.getOriginalNode()
				.getPosition(), node.getOriginalNode().getProcedure(), node
				.getOriginalNode().isErrorLocation(), node.getOriginalNode()
				.getAstNode(), null, null);
		// We have to insert the incoming RootNode into the new model point
		for (IMinimizedEdge edge : node.getIncomingEdges()) {
			if (edge instanceof IMinimizedEdge) {
				IMinimizedEdge minEdge = (IMinimizedEdge) edge;
				if (minEdge.isBasicEdge()) {
					newNode.addIncoming(((IBasicEdge) edge).getOriginalEdge());
				}
			} else {
				throw new IllegalStateException(
						"First Node of a Function, has to start right!");
			}
		}
		// To do the conversion, we need to run over the minimized graph,
		// and convert every edge into an regular RCFG edge
		// ---> to do this we need some special Visitor which does the
		// conversion
		convertVisitor.init(newNode);
		convertVisitor.visitNode(node);
		return newNode;
	}
}
