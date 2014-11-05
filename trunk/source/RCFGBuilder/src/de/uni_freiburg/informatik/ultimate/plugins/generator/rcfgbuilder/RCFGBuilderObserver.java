package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.io.IOException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class RCFGBuilderObserver implements IUnmanagedObserver {

	/**
	 * Root Node of this Ultimate model. I use this to store information that
	 * should be passed to the next plugin. The Sucessors of this node exactly
	 * the initial nodes of procedures.
	 */
	private RootNode mGraphroot;

	/**
	 * Logger for this plugin.
	 */
	private final Logger mLogger;

	private final IUltimateServiceProvider mServices;

	private final IToolchainStorage mStorage;

	public RCFGBuilderObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * 
	 * @return the root of the CFG.
	 */
	public RootNode getRoot() {
		return mGraphroot;
	}

	/**
	 * Copied from CFG Builder
	 * 
	 * Called by the Ultimate Framework. Finds all procedure declarations and
	 * checks whether they're implementations or just declarations. If
	 * implementation is present calls makeProcedureCFG() and appends CFG as
	 * child of procedure node to CFG
	 * @throws IOException 
	 */
	public boolean process(IElement root) throws IOException {
		if (!(root instanceof Unit)) {
			// TODO
			mLogger.debug("No WrapperNode. Let Ultimate process with next node");
			return true;
		} else {
			Unit unit = (Unit) root;
			RCFGBacktranslator translator = new RCFGBacktranslator();
			CfgBuilder recCFGBuilder = new CfgBuilder(unit, translator, mServices, mStorage);
			try {
				mGraphroot = recCFGBuilder.getRootNode(unit);
				ModelUtils.mergeAnnotations(unit, mGraphroot);
				mServices.getBacktranslationService().addTranslator(translator);
			} catch (SMTLIBException e) {
				if (e.getMessage().equals("Cannot create quantifier in quantifier-free logic")) {
					mLogger.warn("Unsupported syntax: " + e.getMessage());
				} else if (e.getMessage().equals("Sort Array not declared")) {
					mLogger.warn("Unsupported syntax: " + e.getMessage());
				} else if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
					mLogger.warn("Unsupported syntax: " + e.getMessage());
				} else {
					throw e;
				}
			}
		}
		return false;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

}
