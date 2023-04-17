package de.uni_freiburg.informatik.ultimate.web.backend;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.EnumSet;

import javax.servlet.DispatcherType;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.server.handler.ContextHandler;
import org.eclipse.jetty.server.handler.ContextHandlerCollection;
import org.eclipse.jetty.server.handler.HandlerCollection;
import org.eclipse.jetty.server.handler.ResourceHandler;
import org.eclipse.jetty.servlet.FilterHolder;
import org.eclipse.jetty.servlet.ServletContextHandler;
import org.eclipse.jetty.servlet.ServletHolder;
import org.eclipse.jetty.util.log.Log;
import org.eclipse.jetty.util.resource.PathResource;

import de.uni_freiburg.informatik.ultimate.web.backend.util.CrossOriginFilter;

public class WebBackend implements IApplication {

	private Server mJettyServer;

	public WebBackend() {
		// no init necessary
	}

	@Override
	public Object start(final IApplicationContext context) throws Exception {
		Config.load();

		initLogging();
		initJettyServer();

		mJettyServer.start();
		mJettyServer.join();

		return EXIT_OK;
	}

	@Override
	public void stop() {
		try {
			mJettyServer.stop();
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}

	private static void initLogging() {
		// Set log level
		System.setProperty("org.eclipse.jetty.LEVEL", Config.LOG_LEVEL);

		if (Config.LOG_FILE_PATH.isEmpty()) {
			Log.getRootLogger().info("Logging to stdout/stderr");
			return;
		}
		// Redirect logging to file.
		FileOutputStream outStream;
		try {
			outStream = new FileOutputStream(Config.LOG_FILE_PATH, true);
			final PrintStream logStream = new PrintStream(outStream);
			System.setOut(logStream);
			System.setErr(logStream);
			Log.getRootLogger().info("Logging to '" + Config.LOG_FILE_PATH + "'");
		} catch (final FileNotFoundException e) {
			Log.getRootLogger().warn("Not able to log to '" + Config.LOG_FILE_PATH + "'");
		}
	}

	/**
	 * Initialize Jetty front- and back-end server.
	 */
	private void initJettyServer() {
		mJettyServer = new Server(Config.PORT);
		final ContextHandlerCollection contexts = new ContextHandlerCollection();
		mJettyServer.setHandler(contexts);

		// Serve the website (front-end) as static content.
		if (Config.SERVE_WEBSITE) {
			final Path absPath = Config.tryGetAbsolutePath(Config.FRONTEND_PATH);
			addStaticPathToContext(contexts, absPath, Config.FRONTEND_ROUTE);
			Log.getRootLogger()
					.info("Serving frontend (" + absPath.toString() + ") at route: " + Config.FRONTEND_ROUTE);
		}

		// Serve the API.
		// Prepare Handler for API servlets.
		final ServletContextHandler servlets = new ServletContextHandler(contexts, "/", ServletContextHandler.SESSIONS);
		// Add the API servlet.
		servlets.addServlet(new ServletHolder(new UltimateApiServlet()), Config.BACKEND_ROUTE + "/*");

		// Enable CORS to allow ultimate back-end/front-end running on a separate port and domain.
		enableCorsOnServletContextHandler(servlets);

		Log.getRootLogger().info("Serving API at route: " + Config.BACKEND_ROUTE);
	}

	/**
	 * Serve files in folderPath static at the routePath.
	 *
	 * @param contextCollection
	 * @param folderPath
	 *            Path to the static files to be served.
	 * @param routePath
	 *            The route the files should be served at (e.g. "/media").
	 */
	private static void addStaticPathToContext(final HandlerCollection contextCollection, final Path folderPath,
			final String routePath) {
		final ResourceHandler frontendResourceHandler = new ResourceHandler();
		frontendResourceHandler.setDirectoriesListed(true);

		final ContextHandler frontendContextHandler = new ContextHandler();
		frontendContextHandler.setContextPath(routePath);
		frontendContextHandler.setBaseResource(new PathResource(folderPath));
		frontendContextHandler.setHandler(frontendResourceHandler);

		contextCollection.addHandler(frontendContextHandler);
	}

	/**
	 * Add CORS headers to the servlets in the servlet handler. Enables the servlets to be called from outside their
	 * served domain.
	 *
	 * @param contexts
	 *            ServletContextHandler
	 */
	private static void enableCorsOnServletContextHandler(final ServletContextHandler contexts) {
		final FilterHolder cors = new FilterHolder(new CrossOriginFilter());
		contexts.addFilter(cors, "/*", EnumSet.of(DispatcherType.REQUEST));

		cors.setInitParameter(CrossOriginFilter.ALLOWED_ORIGINS_PARAM, "*");
		cors.setInitParameter(CrossOriginFilter.ACCESS_CONTROL_ALLOW_ORIGIN_HEADER, "*");
		cors.setInitParameter(CrossOriginFilter.ALLOWED_METHODS_PARAM, "GET,POST");

	}

}
