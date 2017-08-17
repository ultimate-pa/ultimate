package util;

// TODO
public class Timer {
	
	private long time;
	
	public Timer() {
	}
	
	public void start() {
		time = System.currentTimeMillis();
	}
	
	public long getCurrentTime() {
		return System.currentTimeMillis();
	}
	
	public long tick() {
		return System.currentTimeMillis() - time;
	}
	
	public void stop() {
		time = System.currentTimeMillis() - time;
	}
	
	public long getTimeElapsed() {
		return time;
	}

}
