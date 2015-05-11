package de.uni_freiburg.informatik.ultimate.access;

import de.uni_freiburg.informatik.ultimate.model.GraphType;

/**
 * Access to models in Ultimate is managed through observers. UltimateCore
 * expects tools to provide at least one observer that will be executed by
 * UltimateCore.
 * 
 * <p>
 * Note: Implementers should not implement this interface directly, but rather one of
 * it descendants.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public interface IObserver {

	/**
	 * Before an observer is executed on a model, UltimateCore calls
	 * <code>init(...)</code> on the observer. If there are many observers,
	 * <code>init(...)</code> is called on each one. If there are many models,
	 * <code>init(...)</code> is called for each one with increasing
	 * <code>currentModelIndex</code>, e.g. if there are 3 models, an IObserver
	 * lifecycle will be:
	 * <ul>
	 * <li><code>getWalkerOptions()</code>
	 * <li><code>init(...,0,3)</code>
	 * <li><code>process(...)</code> (depending on return value multiple times)
	 * <li><code>finish()</code>
	 * <li><code>performedChanges()</code>
	 * <li><code>getWalkerOptions()</code>
	 * <li><code>init(...,1,3)</code>
	 * <li><code>process(...)</code> (depending on return value multiple times)
	 * <li><code>finish()</code>
	 * <li><code>performedChanges()</code>
	 * <li><code>getWalkerOptions()</code>
	 * <li><code>init(...,2,3)</code>
	 * <li><code>process(...)</code> (depending on return value multiple times)
	 * <li><code>finish()</code>
	 * <li><code>performedChanges()</code>
	 * </ul>
	 * 
	 * @param modelType
	 *            The model type which is about to be executed
	 * @param currentModelIndex
	 *            The current index of the model that is about to be executed
	 * @param numberOfModels
	 *            The total number of models that will be executed by this
	 *            observer
	 * @throws Throwable
	 *             because plugins can fail any way they want during
	 *             {@link #init()} and the core will (try to) handle it.
	 */
	void init(GraphType modelType, int currentModelIndex, int numberOfModels) throws Throwable;

	/**
	 * After an observer has finished executing on a model (or chosen to ignore
	 * it), UlimateCore calls finish() on the observer.
	 * 
	 * @throws Throwable
	 *             because plugins can fail any way they want during
	 *             {@link #finish()} and the core will (try to) handle it.
	 */
	void finish() throws Throwable;

	/**
	 * Before calling init() or executing an observer, UltimateCore calls
	 * getWalkerOptions() to determine, which walker is supposed to be used with
	 * a given observer.
	 * 
	 * @deprecated because the WalkerOptions were never really implemented and
	 *             are consequently not used. Return null here as long as this
	 *             method exists.
	 */
	@Deprecated
	WalkerOptions getWalkerOptions();

	/**
	 * UltimateCore uses this method to determine if a plugin has changed a
	 * model at all.
	 * 
	 * @return true iff this observer has changed a model in any way, false iff
	 *         not.
	 */
	boolean performedChanges();

}
