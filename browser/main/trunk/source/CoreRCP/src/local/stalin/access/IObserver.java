package local.stalin.access;

public interface IObserver {
		
	public abstract void init();
	
	public abstract void finish();
	
	public abstract WalkerOptions getWalkerOptions();
	
	public boolean performedChanges();

}
