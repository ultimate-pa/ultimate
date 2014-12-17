package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

// Inliner for procedures with overall unique variable identifiers.
// TODO implement
public class ProcedureInlinerObserver implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	private Logger mLogger;
	private Unit mAstUnit;

	public ProcedureInlinerObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() throws Throwable {
	}

	@Override
	public void finish() throws Throwable {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false; // TODO change to true, when implemented
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		// Store the first node of the AST and use it to process the AST manually
		if (root instanceof Unit) {
			mAstUnit = (Unit) root;
			// TODO
			// for every non-flat procedure p
			// inline(p, {});
			// --------------------
			// inline(p, parents) :=
			// if p in parents
			// error: possible recursion!
			// for every called procedure c in p
			// if c is not flat
			// inline(c, {p} u parents)
			// inline c into p // this changes p
			// mark p as flat
			return false;
		}
		return true;
	}

}
