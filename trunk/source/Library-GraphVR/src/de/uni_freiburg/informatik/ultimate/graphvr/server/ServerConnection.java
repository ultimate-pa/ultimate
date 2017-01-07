package de.uni_freiburg.informatik.ultimate.graphvr.server;

import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.util.logging.Level;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class ServerConnection implements Runnable {

	protected final ILogger mLogger;
	String clientInput;
	String serverOutput = null;

	Socket connectionSocket = null;

	ServerConnection(Socket connectionSocket, ILogger logger) {
		this.connectionSocket = connectionSocket;
		this.mLogger = logger;
	}

	public void run() {

		try {
			InputStream input = connectionSocket.getInputStream();

			ObjectInputStream inFromClient = new ObjectInputStream(input);

			ObjectOutputStream outToClient = new ObjectOutputStream(connectionSocket.getOutputStream());

			//serveRequest(inFromClient, outToClient);

			outToClient.flush();

		} catch (IOException ex) {
			mLogger.info("Exception occured in ServerConnection run() method");
		}
	}
}