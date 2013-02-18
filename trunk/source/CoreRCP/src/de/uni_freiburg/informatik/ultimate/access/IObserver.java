package de.uni_freiburg.informatik.ultimate.access;

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
	 * Before an observer is executed on a model, UltimateCore calls init() on
	 * the observer. If there are many observers, init() is called repeatedly.
	 */
	public void init();

	/**
	 * After an observer has finished executing on a model (or chosen to ignore
	 * it), UlimateCore calls finish() on the observer.
	 */
	public void finish();

	/**
	 * Before calling init() or executing an observer, UltimateCore calls
	 * getWalkerOptions() to determine, which walker is supposed to be used with
	 * a given observer.
	 * 
	 * Currently, this method is not implemented in UltimateCore, so it is safe to return null here. 
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
