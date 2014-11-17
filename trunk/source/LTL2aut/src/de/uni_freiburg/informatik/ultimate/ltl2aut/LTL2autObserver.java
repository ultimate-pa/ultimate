package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.commons.io.IOUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.AtomicProposition;
import de.uni_freiburg.informatik.ultimate.ltl2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck;

/**
 * This class reads a definition of a property in LTL and returns the AST of the
 * description of the LTL formula as a Buchi automaton.
 * 
 * @author Langenfeld
 * 
 */
public class LTL2autObserver implements IUnmanagedObserver {

	private static final String sLTLMarker = "#LTLProperty:";
	private static final String sIRSMarker = "#IRS:";

	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;
	private final Logger mLogger;

	private String mInputFile;
	private AstNode mRootNode;

	public LTL2autObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() {
		mRootNode = null;
		mInputFile = null;
	}

	@Override
	public void finish() throws Throwable {
		String[] specification = getSpecification();
		if (specification == null || specification.length == 0 || specification[0].isEmpty()) {
			throw new UnsupportedOperationException("No specification given");
		}
		AstNode node = getProperty(specification[0]);
		Map<String, AstNode> irs = getIRS(Arrays.copyOfRange(specification, 1, specification.length));
		new SubstituteAPVisitor(irs, node);
		mLogger.info("LTL Property is: " + specification[0]);
		mLogger.info("IRS table is:");
		for (int i = 1; i < specification.length; ++i) {
			mLogger.info(specification[i]);
		}

		//TODO: Fix 
		new LTLPropertyCheck(getSubstitutedProperty(irs, specification[0]), null, null).annotate(node);
		mRootNode = node;
	}

	private String getSubstitutedProperty(Map<String, AstNode> irs, String property) {
		for (Entry<String, AstNode> entry : irs.entrySet()) {
			property = property.replaceAll(entry.getKey(), "(" + entry.getValue().toString() + ")");
		}
		return property;
	}

	private String[] getSpecification() throws IOException {
		if (PreferenceInitializer.readPropertyFromFile()) {
			if (mInputFile != null) {
				BufferedReader br;
				String line = null;
				ArrayList<String> properties = new ArrayList<>();
				ArrayList<String> irs = new ArrayList<>();
				try {
					br = new BufferedReader(new FileReader(mInputFile));
					while ((line = br.readLine()) != null) {
						if (line.contains(sLTLMarker)) {
							properties.add(line.replaceFirst("//", "").replaceAll(sLTLMarker, "").trim());
						}
						if (line.contains(sIRSMarker)) {
							irs.add(line.replaceFirst("//", "").replaceAll(sIRSMarker, "").trim());
						}
					}
					br.close();
				} catch (IOException e) {
					mLogger.error("Error while reading " + mInputFile + ": " + e);
					line = null;
					throw e;
				}

				if (properties.isEmpty()) {
					mLogger.info("No LTL specification in input file.");
				} else {
					if (properties.size() > 1) {
						throw new UnsupportedOperationException("We currently support only 1 LTL property at a time.");
					}
					String[] rtr = new String[1 + irs.size()];
					rtr[0] = properties.get(0);
					int i = 1;
					for (String entry : irs) {
						rtr[i] = entry;
						i++;
					}
					return rtr;
				}
			}
		}

		mLogger.info("Using LTL specification from settings.");
		String property = new UltimatePreferenceStore(Activator.PLUGIN_ID)
				.getString(PreferenceInitializer.LABEL_PPROPERTY);
		return property.split("\n");
	}

	private AstNode getProperty(String property) throws Throwable {
		try {
			mLogger.debug("Parsing LTL property...");
			return new WrapLTL2Never(mServices, mStorage).ltl2Ast(property);
		} catch (Throwable e) {
			mLogger.fatal(String.format("Exception during LTL->BA execution: %s", e));
			throw e;
		}
	}

	private Map<String, AstNode> getIRS(String[] entries) throws Throwable {
		mLogger.debug("Parsing mapping from AP to boolean expression over program variables...");
		Map<String, AstNode> aps = new HashMap<String, AstNode>();
		for (String entry : entries) {
			try {
				LexerAP lexer = new LexerAP(new InputStreamReader(IOUtils.toInputStream(entry.trim())));
				ParserAP p = new ParserAP(lexer);

				AstNode nodea = (AstNode) p.parse().value;
				// append node to dictionary of atomic propositions
				if (nodea instanceof AtomicProposition) {
					aps.put(((AtomicProposition) nodea).getIdent(), nodea.getOutgoingNodes().get(0));
				}
			} catch (Throwable e) {
				mLogger.error(String.format("Exception while parsing the atomic proposition \"%s\": %s", entry, e));
				throw e;
			}
		}
		return aps;
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
		if (root instanceof Unit) {
			mInputFile = ((Unit) root).getLocation().getFileName();
		}
		return false;
	}

	public AstNode getRootNode() {
		return mRootNode;
	}

}
