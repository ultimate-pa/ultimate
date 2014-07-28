/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * @author dietsch
 * 
 */
public interface IToolchainPlugin extends IUltimatePlugin {

	/**
	 * Ultimate provides every {@link IToolchainPlugin} with an
	 * {@link IToolchainStorage} object. You can store your own service or
	 * storage in this object. It will persist over the lifetime of a toolchain
	 * (i.e. until the next toolchain is run or if the controller explicitly
	 * clears it).
	 * 
	 * @param storage
	 *            Ultimate will provide the toolchain storage object here. This
	 *            object will never be null.
	 */
	void setToolchainStorage(IToolchainStorage storage);

	/**
	 * Through {@link IUltimateServiceProvider} you have access to all services
	 * that Ultimate provides (e.g. ResultReporting, Backtranslation, Logging,
	 * ...).
	 * 
	 * The services can be found in the namespace
	 * de.uni_freiburg.informatik.ultimate.core.services.
	 * 
	 * @param services
	 *            An instance of {@link IUltimateServiceProvider}. This instance
	 *            will never be null.
	 */
	void setServices(IUltimateServiceProvider services);

	/**
	 * {@link UltimateCore} will call this method according to the
	 * UltimatePlugin livecycle (usually once after the plugin has been loaded
	 * and once before it is used in a toolchain).
	 * 
	 * Note that this is called <b>BEFORE</b>
	 * {@link #setServices(IUltimateServiceProvider)} and
	 * {@link #setToolchainStorage(IToolchainStorage)}.
	 */
	int init();
	
	

}
