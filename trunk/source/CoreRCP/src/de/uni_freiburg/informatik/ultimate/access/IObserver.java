package de.uni_freiburg.informatik.ultimate.access;

import de.uni_freiburg.informatik.ultimate.model.GraphType;

/**
 * 
 * Access to models in Ultimate is managed through observers. UltimateCore
 * expects Tools to provide one to many observers that will be executed by
 * UltimateCore. Implementers should not implement this interface directly, but
 * rather it descendants.
 * 
 * @author dietsch
 * 
 */
public interface IObserver {

	/**
	 * Before an observer is executed on a model, UltimateCore calls <code>init(...)</code> on
	 * the observer. If there are many observers, <code>init(...)</code> is called on each one.
	 * If there are many models, <code>init(...)</code> is called for each one with increasing
	 * <code>currentModelIndex</code>, e.g. if there are 3 models, an IObserver lifecycle will be:
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
	 */
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) throws Throwable;

	/**
	 * After an observer has finished executing on a model (or chosen to ignore
	 * it), UlimateCore calls finish() on the observer.
	 * 
	 * @throws Throwable
	 */
	public void finish() throws Throwable;

	/**
	 * Before calling init() or executing an observer, UltimateCore calls
	 * getWalkerOptions() to determine, which walker is supposed to be used with
	 * a given observer.
	 * 
	 * Currently, this method is not implemented in UltimateCore, so it is safe
	 * to return null here.
	 * 
	 * @return
	 */
	public WalkerOptions getWalkerOptions();

	/**
	 * UltimateCore uses this method to determine if a plugin has changed a
	 * model at all.
	 * 
	 * @return true iff this observer has changed a model in any way, false iff
	 *         not.
	 */
	public boolean performedChanges();

}
