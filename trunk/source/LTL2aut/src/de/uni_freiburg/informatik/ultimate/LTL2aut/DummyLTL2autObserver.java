package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.HashMap;

import org.apache.commons.io.IOUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AtomicProposition;
import de.uni_freiburg.informatik.ultimate.LTL2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * This class reads a definition of a property in ltl and returns the AST of the
 * description of the LTL formula as a Buchi automaton.
 * 
 * @author Langenfeld
 * 
 */
public class DummyLTL2autObserver implements IUnmanagedObserver {

	private AstNode mRootNode;
	private Logger mLogger;

	@Override
	public void init() {
		mLogger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
		mRootNode = null;
	}

	@Override
	public void finish() {

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {

		AstNode node;
		String line;

		String property = new UltimatePreferenceStore(Activator.PLUGIN_ID)
				.getString(PreferenceInitializer.LABEL_PPROPERTY);

		BufferedReader br = new BufferedReader(new InputStreamReader(IOUtils.toInputStream(property)));
		try {
			// read the LTLT formula from the first line and pass it to the
			// parser
			line = br.readLine();

			// translate to ba with external tool and get AST
			WrapLTL2Never wrap = new WrapLTL2Never();
			node = wrap.ltl2Ast(line);
		} catch (Throwable e) {
			mLogger.error(String.format("Exception during LTL->BA execution: %s", e));
			throw e;
		}

		try {
			// Read following lines and get Atomic Props
			HashMap<String, AstNode> aps = new HashMap<String, AstNode>(); // ident
																			// ->
																			// propostition
			line = br.readLine();
			while (line != null) {
				LexerAP lexer = new LexerAP(new InputStreamReader(IOUtils.toInputStream(line)));
				ParserAP p = new ParserAP(lexer);
				mLogger.debug("Parsing LTL property...");
				AstNode nodea = (AstNode) p.parse().value;
				// append node to dictionary of atomic propositions
				if (nodea instanceof AtomicProposition)
					aps.put(((AtomicProposition) nodea).getIdent(), nodea.getOutgoingNodes().get(0));

				line = br.readLine();
			}
			// substitute props in AST
			new SubstituteAPVisitor(aps, node);

			this.mRootNode = node;

		} catch (Throwable e) {
			if (line != null) {
				mLogger.error(String.format("Exception while parsing the atomic proposition \"%s\": %s", line, e));
			} else {
				mLogger.error(String.format("Exception while parsing the atomic propositions: %s", e));
			}
			throw e;
		}

		return false;
	}

	public AstNode getRootNode() {
		return mRootNode;
	}

}
