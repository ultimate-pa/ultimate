package de.uni_freiburg.informatik.ultimate.server;

public interface IServer {
	/**
	 * Starts the Server listening to a single connection.
	 */
	void start();

	/**
	 * shuts down the Server.
	 */
	void stop();

}
