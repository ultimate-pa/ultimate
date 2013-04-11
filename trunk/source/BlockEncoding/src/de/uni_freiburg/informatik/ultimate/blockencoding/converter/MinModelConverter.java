/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.converter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.BlockEncodingAnnotation;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.preferences.PreferencePage;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
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
		convertVisitor = new ConversionVisitor(boogie2smt, root,
				getRatingBound());
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
		// Now we have to update the RootAnnot, which is created while executing
		// the RCFGBuilder (this is needed for example for the
		// HoareAnnotations)
		updateRootAnnot(newRoot.getRootAnnot());
		return newRoot;
	}

	/**
	 * Checks the preferences for a given rating bound.
	 * 
	 * @return gets the rating boundary
	 */
	private int getRatingBound() {
		IEclipsePreferences prefs = ConfigurationScope.INSTANCE
				.getNode(Activator.s_PLUGIN_ID);
		String prefValue = prefs.get(PreferencePage.NAME_RATINGBOUND, "");
		// if there is no boundary value given, we do Large Block Encoding
		if (prefValue.equals("")) {
			return -1;
		}
		try {
			return Integer.parseInt(prefValue);
		} catch (NumberFormatException e) {
			s_Logger.error("Value in Preferences is not numeric,"
					+ " Large Block Encoding is applied");
			return -1;
		}
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
		ProgramPoint newNode = convertVisitor.getReferencedNode(node);
		// To do the conversion, we need to run over the minimized graph,
		// and convert every edge into an regular RCFG edge
		// ---> to do this we need some special Visitor which does the
		// conversion
		convertVisitor.init(newNode);
		convertVisitor.visitNode(node);
		return newNode;
	}

	/**
	 * We have to update some Maps, which are stored in the RootAnnot. They are
	 * needed for several computations afterwards. Most of the maps are usual
	 * very small, so that iterating over them should be not that expensive. One
	 * exception is the field "locNodes", there is every ProgramPoint stored,
	 * with its name and the procedure name. We store during the conversion.
	 * 
	 * @param rootAnnot
	 */
	private void updateRootAnnot(RootAnnot rootAnnot) {
		HashMap<ProgramPoint, ProgramPoint> progPointMap = convertVisitor
				.getOrigToNewMap();
		// Update the Entry-Nodes
		HashMap<String, ProgramPoint> entryNodes = new HashMap<String, ProgramPoint>(
				rootAnnot.getEntryNodes());
		rootAnnot.getEntryNodes().clear();
		for (String key : entryNodes.keySet()) {
			ProgramPoint oldVal = entryNodes.get(key);
			if (progPointMap.containsKey(oldVal)) {
				rootAnnot.getEntryNodes().put(key, progPointMap.get(oldVal));
			}
		}
		// Update the Exit-Nodes
		HashMap<String, ProgramPoint> exitNodes = new HashMap<String, ProgramPoint>(
				rootAnnot.getExitNodes());
		rootAnnot.getExitNodes().clear();
		for (String key : exitNodes.keySet()) {
			ProgramPoint oldVal = exitNodes.get(key);
			if (progPointMap.containsKey(oldVal)) {
				rootAnnot.getExitNodes().put(key, progPointMap.get(oldVal));
			}
		}
		// Update the Error-Nodes
		for (String key : rootAnnot.getErrorNodes().keySet()) {
			ArrayList<ProgramPoint> newReferences = new ArrayList<ProgramPoint>();
			for (ProgramPoint oldVal : rootAnnot.getErrorNodes().get(key)) {
				if (progPointMap.containsKey(oldVal)) {
					newReferences.add(progPointMap.get(oldVal));
				} else {
					s_Logger.warn("There is no correspondent node in the"
							+ " new graph for the error location " + oldVal);
				}
			}
			rootAnnot.getErrorNodes().put(key, newReferences);
		}
		// Update the LoopLocations
		// Attention: ProgramPoint implements equals, we have to care for that!
		HashSet<ProgramPoint> keySet = new HashSet<ProgramPoint>(rootAnnot
				.getLoopLocations().keySet());
		rootAnnot.getLoopLocations().clear();
		for (ProgramPoint oldVal : keySet) {
			if (progPointMap.containsKey(oldVal)) {
				ProgramPoint newVal = progPointMap.get(oldVal);
				if (newVal.getAstNode() != null) {
					// Since hashCode(oldVal) == hashCode(newVal), this line
					// overwrites the old entry, so that we do not remove it in
					// the end!
					rootAnnot.getLoopLocations().put(newVal,
							newVal.getAstNode().getLocation());
				}
			}
		}
		// update the locNodes, we rely here on the visitor
		rootAnnot.getProgramPoints().clear();
		rootAnnot.getProgramPoints().putAll(
				convertVisitor.getLocNodesForAnnot());
	}
}
