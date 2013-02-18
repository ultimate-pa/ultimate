;;; scion.el --- Haskell Minor Mode for Interacting with the Scion Library
;;
;;;; License
;;     Copyright (C) 2003  Eric Marsden, Luke Gorrie, Helmut Eller
;;     Copyright (C) 2004,2005,2006  Luke Gorrie, Helmut Eller
;;     Copyright (C) 2008  Thomas Schilling
;;
;;     This program is free software; you can redistribute it and/or
;;     modify it under the terms of the GNU General Public License as
;;     published by the Free Software Foundation; either version 2 of
;;     the License, or (at your option) any later version.
;;
;;     This program is distributed in the hope that it will be useful,
;;     but WITHOUT ANY WARRANTY; without even the implied warranty of
;;     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;;     GNU General Public License for more details.
;;
;;     You should have received a copy of the GNU General Public
;;     License along with this program; if not, write to the Free
;;     Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;;     MA 02111-1307, USA.

;;;; Dependencies and setup

(eval-and-compile
  (require 'cl)
  (require 'json)
  (unless (fboundp 'define-minor-mode)
    (require 'easy-mmode)
    (defalias 'define-minor-mode 'easy-mmode-define-minor-mode)))
(require 'hideshow)
(require 'thingatpt)
(require 'comint)
(require 'ido)
(eval-when (compile)
  (require 'apropos)
  (require 'outline)
  ;; (require 'etags)
  )


;;;---------------------------------------------------------------------------
;;;; Customize groups
;; 
;;;;; scion

(defgroup scion nil
  "Interaction with the Scion Server."
  :prefix "scion-"
  :group 'applications)

;;;;; scion-ui

(defgroup scion-ui nil
  "Interaction with the Scion Server."
  :prefix "scion-"
  :group 'scion)

(defcustom scion-kill-without-query-p nil
  "If non-nil, kill SCION processes without query when quitting Emacs.
This applies to the *inferior-lisp* buffer and the network connections."
  :type 'boolean
  :group 'scion-ui)

;;;;; scion-haskell

(defgroup scion-haskell nil
  "Haskell server configuration."
  :prefix "scion-"
  :group 'scion)

(defcustom scion-connected-hook nil
  "List of functions to call when SCION connects to Haskell."
  :type 'hook
  :group 'scion-haskell)

(defcustom scion-haskell-host "127.0.0.1"
  "The default hostname (or IP address) to connect to."
  :type 'string
  :group 'scion-haskell)

(defcustom scion-port 4005
  "Port to use as the default for `scion-connect'."
  :type 'integer
  :group 'scion-haskell)

(make-variable-buffer-local
 (defvar scion-modeline-string nil
   "The string that should be displayed in the modeline if
`scion-extended-modeline' is true, and which indicates the
current connection, package and state of a Lisp buffer.
The string is periodically updated by an idle timer."))

;;;---------------------------------------------------------------------------

;;;; Macros

(defmacro* when-let ((var value) &rest body)
  "Evaluate VALUE, and if the result is non-nil bind it to VAR and
evaluate BODY.

\(fn (VAR VALUE) &rest BODY)"
  `(let ((,var ,value))
     (when ,var ,@body)))

(defmacro destructure-case (value &rest patterns)
  "Dispatch VALUE to one of PATTERNS.
A cross between `case' and `destructuring-bind'.
The pattern syntax is:
  ((HEAD . ARGS) . BODY)
The list of patterns is searched for a HEAD `eq' to the car of
VALUE. If one is found, the BODY is executed with ARGS bound to the
corresponding values in the CDR of VALUE."
  (let ((operator (gensym "op-"))
	(operands (gensym "rand-"))
	(tmp (gensym "tmp-")))
    `(let* ((,tmp ,value)
	    (,operator (car ,tmp))
	    (,operands (cdr ,tmp)))
       (case ,operator
	 ,@(mapcar (lambda (clause)
                     (if (eq (car clause) t)
                         `(t ,@(cdr clause))
                       (destructuring-bind ((op &rest rands) &rest body) clause
                         `(,op (destructuring-bind ,rands ,operands
                                 . ,body)))))
		   patterns)
	 ,@(if (eq (caar (last patterns)) t)
	       '()
	     `((t (error "Elisp destructure-case failed: %S" ,tmp))))))))

(put 'destructure-case 'lisp-indent-function 1)

;;;; Temporary Popup Buffers

;; Interface
(defmacro* scion-with-popup-buffer ((name &optional package
                                          connection emacs-snapshot)
                                    &body body)
  "Similar to `with-output-to-temp-buffer'.
Bind standard-output and initialize some buffer-local variables.
Restore window configuration when closed.

NAME is the name of the buffer to be created.
PACKAGE is the value `scion-buffer-package'.
CONNECTION is the value for `scion-buffer-connection'.
If nil, no explicit connection is associated with
the buffer.  If t, the current connection is taken.

If EMACS-SNAPSHOT is non-NIL, it's used to restore the previous
state of Emacs after closing the temporary buffer. Otherwise, the
current state will be saved and later restored."
  `(let* ((vars% (list ,(if (eq package t) '(scion-current-package) package)
                       ,(if (eq connection t) '(scion-connection) connection)
                       ;; Defer the decision for NILness until runtime.
                       (or ,emacs-snapshot (scion-current-emacs-snapshot))))
          (standard-output (scion-popup-buffer ,name vars%)))
     (with-current-buffer standard-output
       (prog1 (progn ,@body)
         (assert (eq (current-buffer) standard-output))
         (setq buffer-read-only t)
         (scion-init-popup-buffer vars%)))))

(put 'scion-with-popup-buffer 'lisp-indent-function 1)

(defmacro* with-struct ((conc-name &rest slots) struct &body body)
  "Like with-slots but works only for structs.
\(fn (CONC-NAME &rest SLOTS) STRUCT &body BODY)"
  (flet ((reader (slot) (intern (concat (symbol-name conc-name)
					(symbol-name slot)))))
    (let ((struct-var (gensym "struct")))
      `(let ((,struct-var ,struct))
	 (symbol-macrolet
	     ,(mapcar (lambda (slot)
			(etypecase slot
			  (symbol `(,slot (,(reader slot) ,struct-var)))
			  (cons `(,(first slot) (,(reader (second slot)) 
						 ,struct-var)))))
		      slots)
	   . ,body)))))

(put 'with-struct 'lisp-indent-function 2)

(defmacro scion-define-keys (keymap &rest key-command)
  "Define keys in KEYMAP. Each KEY-COMMAND is a list of (KEY COMMAND)."
  `(progn . ,(mapcar (lambda (k-c) `(define-key ,keymap . ,k-c))
		     key-command)))

(put 'slime-define-keys 'lisp-indent-function 1)

(defvar scion-completing-read-function 'completing-read
  "The completion function used by scion.

You might prefer `ido-completing-read' to the default, but that
leads to problems on some versions of Emacs which are so severe
that Emacs needs to be restarted. (You have been warned!)")

(defun scion-completing-read (prompt collection &optional predicate require-match
				     initial-input hist def inherit-input-method)
  (if (eq scion-completing-read-function 'ido-completing-read)
      ;; ido-completing-read does not support the last argument.  What
      ;; a mess.
      (funcall scion-completing-read-function 
	   prompt collection predicate require-match initial-input
	   hist def)
    (funcall scion-completing-read-function 
	   prompt collection predicate require-match initial-input
	   hist def inherit-input-method)))

;;;---------------------------------------------------------------------------
;;;;;; Tree View Widget

(defstruct (scion-tree (:conc-name scion-tree.))
  item
  (print-fn #'scion-tree-default-printer :type function)
  (kids '() :type list)
  (collapsed-p t :type boolean)
  (prefix "" :type string)
  (start-mark nil)
  (end-mark nil)
  (plist '() :type list))

(defun scion-tree-leaf-p (tree)
  (not (scion-tree.kids tree)))

(defun scion-tree-default-printer (tree)
  (princ (scion-tree.item tree) (current-buffer)))

(defun scion-tree-decoration (tree)
  (cond ((scion-tree-leaf-p tree) "-- ")
	((scion-tree.collapsed-p tree) "[+] ")
	(t "-+  ")))

(defun scion-tree-insert-list (list prefix)
  "Insert a list of trees."
  (loop for (elt . rest) on list 
	do (cond (rest
		  (insert prefix " |")
		  (scion-tree-insert elt (concat prefix " |"))
                  (insert "\n"))
		 (t
		  (insert prefix " `")
		  (scion-tree-insert elt (concat prefix "  "))))))

(defun scion-tree-insert-decoration (tree)
  (insert (scion-tree-decoration tree)))

(defun scion-tree-indent-item (start end prefix)
  "Insert PREFIX at the beginning of each but the first line.
This is used for labels spanning multiple lines."
  (save-excursion
    (goto-char end)
    (beginning-of-line)
    (while (< start (point))
      (insert-before-markers prefix)
      (forward-line -1))))

(defun scion-tree-insert (tree prefix)
  "Insert TREE prefixed with PREFIX at point."
  (with-struct (scion-tree. print-fn kids collapsed-p start-mark end-mark) tree
    (let ((line-start (line-beginning-position)))
      (setf start-mark (point-marker))
      (scion-tree-insert-decoration tree)
      (funcall print-fn tree)
      (scion-tree-indent-item start-mark (point) (concat prefix "   "))
      (add-text-properties line-start (point) (list 'scion-tree tree))
      (set-marker-insertion-type start-mark t)
      (when (and kids (not collapsed-p))
        (terpri (current-buffer))
        (scion-tree-insert-list kids prefix))
      (setf (scion-tree.prefix tree) prefix)
      (setf end-mark (point-marker)))))

(defun scion-tree-at-point ()
  (cond ((get-text-property (point) 'scion-tree))
        (t (error "No tree at point"))))

(defun scion-tree-delete (tree)
  "Delete the region for TREE."
  (delete-region (scion-tree.start-mark tree)
                 (scion-tree.end-mark tree)))

(defun scion-tree-toggle (tree)
  "Toggle the visibility of TREE's children."
  (with-struct (scion-tree. collapsed-p start-mark end-mark prefix) tree
    (setf collapsed-p (not collapsed-p))
    (scion-tree-delete tree)
    (insert-before-markers " ") ; move parent's end-mark
    (backward-char 1)
    (scion-tree-insert tree prefix)
    (delete-char 1)
    (goto-char start-mark)))


;;;---------------------------------------------------------------------------

(defvar scion-program "scion-server"
  "Program name of the Scion server.")

(defvar scion-last-compilation-result nil
  "The result of the most recently issued compilation.")


(make-variable-buffer-local
 (defvar scion-mode-line " Scion"))

(define-minor-mode scion-mode
  "\\<scion-mode-map>\
Scion: Smart Haskell mode.
\\{scion-mode-map}"
  nil
  scion-mode-line
  ;; Fake binding to coax `define-minor-mode' to create the keymap
  '((" " 'self-insert-command))
  (when scion-last-compilation-result
    (scion-highlight-notes (scion-compiler-notes) (current-buffer))))

(define-key scion-mode-map " " 'self-insert-command)

;; dummy definitions for the compiler
(defvar scion-net-coding-system)
(defvar scion-net-processes)
(defvar scion-default-connection)

(defun scion (&optional command)
  "Start a Scion server and connect to it."
  (interactive)
  (let ((server-program (or command scion-program)))
    (scion-start :program server-program)))

(defun* scion-start (&key (program scion-program)
			  program-args
			  env
			  directory
			  name
			  (buffer "*scion-server*"))
  (let ((proc (scion-maybe-start-server program program-args env
					directory buffer)))
    ))

(defun scion-maybe-start-server (program program-args env directory buffer)
  (cond
   ((not (comint-check-proc buffer))
    (scion-start-server program program-args env directory buffer))
   (t
    (message "Scion server is already running")
    nil)))

(defvar scion-connect-buffer nil
  "Buffer that is currently trying to connect to a Scion server.")

(defun scion-start-server (program program-args env directory buffer)
  (with-current-buffer (get-buffer-create buffer)
    (when directory
      (cd (expand-file-name directory)))
    (delete-region (point-min) (point-max))
    (comint-mode)
    (setq scion-connect-buffer (current-buffer))
    (message "Connecting... (Abort with `M-x scion-abort-connect`.)")
    (add-hook 'comint-output-filter-functions 
              'scion-check-server-ready nil t)
    (let ((process-environment (append env process-environment)))
      (comint-exec (current-buffer) "scion-emacs" program nil program-args))
    (let ((proc (get-buffer-process (current-buffer))))
      ; (scion-set-query-on-exit-flag proc)
      proc)))

(defun scion-check-server-ready (server-output)
  "Watches the server's output for the port number to connect to."
  (let* ((regexp "^=== Listening on port: \\([0-9]+\\)$")
         (port (save-excursion
                 (goto-char (point-min))
                 (when (re-search-forward regexp nil t)
                   (read (match-string 1)) ))))
    (when port
      (remove-hook 'comint-output-filter-functions 
                   'scion-check-server-ready t)
      (setq scion-connect-buffer nil)
      (sleep-for 0.1)  ;; give the server some time to get connected
      (scion-connect "127.0.0.1" port))))

(defun scion-abort-connect ()
  "Abort the current connection attempt."
  (interactive)
  (cond (scion-connect-buffer
         (kill-buffer scion-connect-buffer)
         (message "Connection attempt aborted."))
        (t
         (error "Not connecting."))))

(defun scion-connect (host port &optional coding-system)
  "Connect to a running Swank server."
  (interactive (list (read-from-minibuffer "Host: " scion-haskell-host)
                     (read-from-minibuffer "Port: " (format "%d" scion-port)
                                           nil t)))
  (when (and (interactive-p) scion-net-processes
             (y-or-n-p "Close old connections first? "))
    (scion-disconnect))
  (message "Connecting to Scion Server on port %S.." port)
  (let ((coding-system (or coding-system scion-net-coding-system)))
    (scion-check-coding-system coding-system)
    (message "Connecting to Scion Server on port %S.." port)
    (let* ((process (scion-net-connect host port coding-system))
           (scion-dispatching-connection process))
      (scion-setup-connection process))))

;;;---------------------------------------------------------------------------
;;;; Networking
;;;---------------------------------------------------------------------------
;;;
;;; This section covers the low-level networking: establishing
;;; connections and encoding/decoding protocol messages.
;;;
;;; Each SCION protocol message begins with a 3-byte length header
;;; followed by an S-expression as text. [XXX: The sexp must be readable
;;; both by Emacs and by Common Haskell, so if it contains any embedded
;;; code fragments they should be sent as strings.]
;;;
;;; The set of meaningful protocol messages are not specified
;;; here. They are defined elsewhere by the event-dispatching
;;; functions in this file and in Scion/Server/Emacs.hs.

(defvar scion-net-processes nil
  "List of processes (sockets) connected to Haskell.")

(defvar scion-net-process-close-hooks '()
  "List of functions called when a scion network connection closes.
The functions are called with the process as their argument.")

(defun scion-secret ()
  "Finds the magic secret from the user's home directory.
Returns nil if the file doesn't exist or is empty; otherwise the first
line of the file."
  nil) 					; disable for now

;;;---------------------------------------------------------------------------
;;; Interface

(defun scion-net-connect (host port coding-system)
  "Establish a connection with a Scion Server.

<hostname> <port> <coding-system> -> <network-stream-process>"
  (let* ((inhibit-quit nil)
         (proc (open-network-stream "Scion Server" nil host port))
         (buffer (scion-make-net-buffer " *scion-connection*")))
    (push proc scion-net-processes)
    (set-process-buffer proc buffer)
    (set-process-filter proc 'scion-net-filter)
    (set-process-sentinel proc 'scion-net-sentinel)
    (scion-set-query-on-exit-flag proc)
    (when (fboundp 'set-process-coding-system)
      (scion-check-coding-system coding-system)
      (set-process-coding-system proc coding-system coding-system))
    (when-let (secret (scion-secret))
      (scion-net-send secret proc))
    proc))

(defun scion-make-net-buffer (name)
  "Make a buffer suitable for a network process."
  (let ((buffer (generate-new-buffer name)))
    (with-current-buffer buffer
      (buffer-disable-undo))
    buffer))

(defun scion-set-query-on-exit-flag (process)
  "Set PROCESS's query-on-exit-flag to `scion-kill-without-query-p'."
  (when scion-kill-without-query-p
    ;; avoid byte-compiler warnings
    (let ((fun (if (fboundp 'set-process-query-on-exit-flag)
                   'set-process-query-on-exit-flag
                 'process-kill-without-query)))
      (funcall fun process nil))))


;;;---------------------------------------------------------------------------
;;;;; Coding system madness

(defvar scion-net-valid-coding-systems
  '((iso-latin-1-unix nil "iso-latin-1-unix")
    (iso-8859-1-unix  nil "iso-latin-1-unix")
    (binary           nil "iso-latin-1-unix")
    (utf-8-unix       t   "utf-8-unix")
;;     (emacs-mule-unix  t   "emacs-mule-unix")
;;     (euc-jp-unix      t   "euc-jp-unix")
    )
  "A list of valid coding systems. 
Each element is of the form: (NAME MULTIBYTEP CL-NAME)")

(defun scion-find-coding-system (name)
  "Return the coding system for the symbol NAME.
The result is either an element in `scion-net-valid-coding-systems'
or NIL."
  (let* ((probe (assq name scion-net-valid-coding-systems)))
    (if (and probe (if (fboundp 'check-coding-system)
                       (ignore-errors (check-coding-system (car probe)))
                     (eq (car probe) 'binary)))
        probe)))

(defvar scion-net-coding-system
  (find-if 'scion-find-coding-system 
           '(iso-latin-1-unix iso-8859-1-unix binary))
  "*Coding system used for network connections.
See also `scion-net-valid-coding-systems'.")
  
(defun scion-check-coding-system (coding-system)
  "Signal an error if CODING-SYSTEM isn't a valid coding system."
  (interactive)
  (let ((props (scion-find-coding-system coding-system)))
    (unless props
      (error "Invalid scion-net-coding-system: %s. %s"
             coding-system (mapcar #'car scion-net-valid-coding-systems)))
    (when (and (second props) (boundp 'default-enable-multibyte-characters))
      (assert default-enable-multibyte-characters))
    t))

(defcustom scion-repl-history-file-coding-system 
  (cond ((scion-find-coding-system 'utf-8-unix) 'utf-8-unix)
        (t scion-net-coding-system))
  "*The coding system for the history file."
  :type 'symbol
  :group 'scion-repl)

(defun scion-coding-system-mulibyte-p (coding-system)
  (second (scion-find-coding-system coding-system)))

(defun scion-coding-system-cl-name (coding-system)
  (third (scion-find-coding-system coding-system)))

;;;---------------------------------------------------------------------------
;;; Interface

(defun scion-net-send (sexp proc)
  "Send a SEXP to Lisp over the socket PROC.
This is the lowest level of communication. The sexp will be READ and
EVAL'd by Lisp."
  (let* ((json-object-type 'plist)
	 (json-key-type 'keyword)
	 (json-array-type 'list)
	 (string (concat (json-encode sexp) "\n"))
	 ;; (string (concat (scion-net-encode-length (length msg)) msg))
         (coding-system (cdr (process-coding-system proc))))
    (scion-log-event sexp)
    (cond ((scion-safe-encoding-p coding-system string)
           (process-send-string proc string))
          (t (error "Coding system %s not suitable for %S"
                    coding-system string)))))

(defun scion-safe-encoding-p (coding-system string)
  "Return true iff CODING-SYSTEM can safely encode STRING."
  (if (featurep 'xemacs)
      ;; FIXME: XEmacs encodes non-encodeable chars as ?~ automatically
      t
    (or (let ((candidates (find-coding-systems-string string))
              (base (coding-system-base coding-system)))
          (or (equal candidates '(undecided))
              (memq base candidates)))
        (and (not (multibyte-string-p string))
             (not (scion-coding-system-mulibyte-p coding-system))))))

(defun scion-net-close (process &optional debug)
  (setq scion-net-processes (remove process scion-net-processes))
  (when (eq process scion-default-connection)
    (setq scion-default-connection nil))
  (cond (debug         
         (set-process-sentinel process 'ignore)
         (set-process-filter process 'ignore)
         (delete-process process))
        (t
         (run-hook-with-args 'scion-net-process-close-hooks process)
         ;; killing the buffer also closes the socket
         (kill-buffer (process-buffer process)))))

(defun scion-net-sentinel (process message)
  (message "Connection to Scion server closed unexpectedly: %s" message)
  (scion-net-close process))

;;; Socket input is handled by `scion-net-filter', which decodes any
;;; complete messages and hands them off to the event dispatcher.

(defun scion-net-filter (process string)
  "Accept output from the socket and process all complete messages."
  (condition-case ex
      (progn
	(with-current-buffer (process-buffer process)
	  (goto-char (point-max))
	  (insert string))
	(scion-process-available-input process))
    ('error 
     (message "Error in process filter: %s" ex)
     nil)))

(defun scion-process-available-input (process)
  "Process all complete messages that have arrived from Lisp."
  (with-current-buffer (process-buffer process)
    (while (scion-net-have-input-p)
      (let ((event (scion-net-read-or-lose process))
            (ok nil))
        (scion-log-event event)
        (unwind-protect
            (save-current-buffer
              (scion-dispatch-event event process)
              (setq ok t))
          (unless ok
            (scion-run-when-idle 'scion-process-available-input process)))))))

(defun scion-net-have-input-p ()
  "Return true if a complete message is available."
  (goto-char (point-min))
  ;; A message is terminated by a newline.
  (search-forward "\n" nil t))

(defun scion-run-when-idle (function &rest args)
  "Call FUNCTION as soon as Emacs is idle."
  (apply #'run-at-time 
         (if (featurep 'xemacs) itimer-short-interval 0) 
         nil function args))

(defun scion-net-read-or-lose (process)
  (condition-case net-read-error
      (scion-net-read)
    (net-read-error
     ;; (debug)
     (scion-net-close process t)
     (error "net-read error: %S" net-read-error))))

(defun scion-net-read ()
  "Read a message from the network buffer."
  (goto-char (point-min))
  (let ((json-object-type 'plist)
	(json-key-type 'keyword)
	(json-array-type 'list))
    (let* ((start (point))
	   (message (json-read))
	   (end (min (1+ (point)) (point-max))))
      ;; TODO: handle errors somehow
      (delete-region start end)
      message)))

(defun scion-net-decode-length ()
  "Read a 24-bit hex-encoded integer from buffer."
  (string-to-number (buffer-substring-no-properties (point) (+ (point) 6)) 16))

(defun scion-net-encode-length (n)
  "Encode an integer into a 24-bit hex string."
  (format "%06x" n))

(defun scion-prin1-to-string (sexp)
  "Like `prin1-to-string' but don't octal-escape non-ascii characters.
This is more compatible with the CL reader."
  (with-temp-buffer
    (let (print-escape-nonascii
          print-escape-newlines
          print-length 
          print-level)
      (prin1 sexp (current-buffer))
      (buffer-string))))

;;;---------------------------------------------------------------------------


;;;; Connections
;;;
;;; "Connections" are the high-level Emacs<->Lisp networking concept.
;;;
;;; Emacs has a connection to each Lisp process that it's interacting
;;; with. Typically there would only be one, but a user can choose to
;;; connect to many Lisps simultaneously.
;;;
;;; A connection consists of a control socket, optionally an extra
;;; socket dedicated to receiving Lisp output (an optimization), and a
;;; set of connection-local state variables.
;;;
;;; The state variables are stored as buffer-local variables in the
;;; control socket's process-buffer and are used via accessor
;;; functions. These variables include things like the *FEATURES* list
;;; and Unix Pid of the Lisp process.
;;;
;;; One connection is "current" at any given time. This is:
;;;   `scion-dispatching-connection' if dynamically bound, or
;;;   `scion-buffer-connection' if this is set buffer-local, or
;;;   `scion-default-connection' otherwise. 
;;;
;;; When you're invoking commands in your source files you'll be using
;;; `scion-default-connection'. This connection can be interactively
;;; reassigned via the connection-list buffer.
;;;
;;; When a command creates a new buffer it will set
;;; `scion-buffer-connection' so that commands in the new buffer will
;;; use the connection that the buffer originated from. For example,
;;; the apropos command creates the *Apropos* buffer and any command
;;; in that buffer (e.g. `M-.') will go to the same Lisp that did the
;;; apropos search. REPL buffers are similarly tied to their
;;; respective connections.
;;;
;;; When Emacs is dispatching some network message that arrived from a
;;; connection it will dynamically bind `scion-dispatching-connection'
;;; so that the event will be processed in the context of that
;;; connection.
;;;
;;; This is mostly transparent. The user should be aware that he can
;;; set the default connection to pick which Lisp handles commands in
;;; Lisp-mode source buffers, and scion hackers should be aware that
;;; they can tie a buffer to a specific connection. The rest takes
;;; care of itself.

(defvar scion-dispatching-connection nil
  "Network process currently executing.
This is dynamically bound while handling messages from Lisp; it
overrides `scion-buffer-connection' and `scion-default-connection'.")

(make-variable-buffer-local
 (defvar scion-buffer-connection nil
   "Network connection to use in the current buffer.
This overrides `scion-default-connection'."))

(defvar scion-default-connection nil
  "Network connection to use by default.
Used for all Lisp communication, except when overridden by
`scion-dispatching-connection' or `scion-buffer-connection'.")

(defun scion-current-connection ()
  "Return the connection to use for Lisp interaction.
Return nil if there's no connection."
  (or scion-dispatching-connection
      scion-buffer-connection
      scion-default-connection))

(defun scion-connection ()
  "Return the connection to use for Lisp interaction.
Signal an error if there's no connection."
  (let ((conn (scion-current-connection)))
    (cond ((and (not conn) scion-net-processes)
           (or (scion-auto-select-connection)
               (error "No default connection selected.")))
          ((not conn)
           (or (scion-auto-connect)
               (error "Not connected.")))
          ((not (eq (process-status conn) 'open))
           (error "Connection closed."))
          (t conn))))

(defvar scion-auto-connect 'always)

(defun scion-auto-connect ()
  (cond ((or (eq scion-auto-connect 'always)
             (and (eq scion-auto-connect 'ask)
                  (y-or-n-p "No connection.  Start Scion? ")))
         (save-window-excursion
           (scion) ; XXX
           (while (not (scion-current-connection))
             (sleep-for 1))
           (scion-connection)))
        (t nil)))

(defvar scion-auto-select-connection 'ask)

(defun scion-auto-select-connection ()
  (let* ((c0 (car scion-net-processes))
         (c (cond ((eq scion-auto-select-connection 'always) c0)
                  ((and (eq scion-auto-select-connection 'ask)
                        (y-or-n-p 
                         (format "No default connection selected.  %s %s? "
                                 "Switch to" (scion-connection-name c0))))
                   c0))))
    (when c
      (scion-select-connection c)
      (message "Switching to connection: %s" (scion-connection-name c))
      c)))

(defun scion-select-connection (process)
  "Make PROCESS the default connection."
  (setq scion-default-connection process))

(defun scion-cycle-connections ()
  "Change current scion connection, and make it buffer local."
  (interactive)
  (let* ((tail (or (cdr (member (scion-current-connection)
                                scion-net-processes))
                   scion-net-processes))
         (p (car tail)))
    (scion-select-connection p)
    (unless (eq major-mode 'scion-repl-mode)
      (setq scion-buffer-connection p))
    (message "Lisp: %s %s" (scion-connection-name p) (process-contact p))))

(defmacro* scion-with-connection-buffer ((&optional process) &rest body)
  "Execute BODY in the process-buffer of PROCESS.
If PROCESS is not specified, `scion-connection' is used.

\(fn (&optional PROCESS) &body BODY))"
  `(with-current-buffer
       (process-buffer (or ,process (scion-connection)
                           (error "No connection")))
     ,@body))

(put 'scion-with-connection-buffer 'lisp-indent-function 1)

(defun scion-connected-p ()
  "Return true if the Swank connection is open."
  (not (null scion-net-processes)))

(defun scion-compute-connection-state (conn)
  (cond ((null conn) :disconnected) 
        ;((scion-stale-connection-p conn) :stale)
        ;((scion-debugged-connection-p conn) :debugged)
        ((and (scion-use-sigint-for-interrupt conn) 
              (scion-busy-p conn)) :busy)
        ((eq scion-buffer-connection conn) :local)
        (t :connected)))

(defun scion-connection-state-as-string (state)
  (case state
    (:connected       "")
    (:disconnected    "not connected")
    (:busy            "busy..")
    (:debugged        "debugged..")
    (:stale           "stale")
    (:local           "local")
    ))

;;; Connection-local variables:

(defmacro scion-def-connection-var (varname &rest initial-value-and-doc)
  "Define a connection-local variable.
The value of the variable can be read by calling the function of the
same name (it must not be accessed directly). The accessor function is
setf-able.

The actual variable bindings are stored buffer-local in the
process-buffers of connections. The accessor function refers to
the binding for `scion-connection'."
  (let ((real-var (intern (format "%s:connlocal" varname))))
    `(progn
       ;; Variable
       (make-variable-buffer-local
        (defvar ,real-var ,@initial-value-and-doc))
       ;; Accessor
       (defun ,varname (&optional process)
         (scion-with-connection-buffer (process) ,real-var))
       ;; Setf
       (defsetf ,varname (&optional process) (store)
         `(scion-with-connection-buffer (,process)
            (setq (\, (quote (\, real-var))) (\, store))
            (\, store)))
       '(\, varname))))

(put 'scion-def-connection-var 'lisp-indent-function 2)

;; Let's indulge in some pretty colours.
(unless (featurep 'xemacs)
  (font-lock-add-keywords
   'emacs-lisp-mode
   '(("(\\(scion-def-connection-var\\)\\s +\\(\\(\\w\\|\\s_\\)+\\)"
      (1 font-lock-keyword-face)
      (2 font-lock-variable-name-face)))))

(scion-def-connection-var scion-connection-number nil
  "Serial number of a connection.
Bound in the connection's process-buffer.")

(scion-def-connection-var scion-pid nil
  "The process id of the Haskell process.")

(scion-def-connection-var scion-connection-name nil
  "The short name for connection.")

;;;;; Connection setup

(defvar scion-connection-counter 0
  "The number of SCION connections made. For generating serial numbers.")

;;; Interface
(defun scion-setup-connection (process)
  "Make a connection out of PROCESS."
  (let ((scion-dispatching-connection process))
    (scion-init-connection-state process)
    (scion-select-connection process)
    process))

(defun scion-init-connection-state (proc)
  "Initialize connection state in the process-buffer of PROC."
  ;; To make life simpler for the user: if this is the only open
  ;; connection then reset the connection counter.
  (when (equal scion-net-processes (list proc))
    (setq scion-connection-counter 0))
  (scion-with-connection-buffer ()
    (setq scion-buffer-connection proc))
  (setf (scion-connection-number proc) (incf scion-connection-counter))
  ;; We do the rest of our initialization asynchronously. The current
  ;; function may be called from a timer, and if we setup the REPL
  ;; from a timer then it mysteriously uses the wrong keymap for the
  ;; first command.
  (scion-eval-async '("connection-info")
                    (scion-curry #'scion-set-connection-info proc)))

(defun scion-set-connection-info (connection info)
  "Initialize CONNECTION with INFO received from Lisp."
  (let ((scion-dispatching-connection connection))
    (destructuring-bind (&key pid version
                              &allow-other-keys) info
      (scion-check-version version connection)
      (setf (scion-pid) pid
	    (scion-connection-name) (format "%d" pid)))
    (let ((args nil))
      (run-hooks 'scion-connected-hook))
    (message "Connected.")))

(defvar scion-protocol-version 1)

(defun scion-check-version (version conn)
  (or (equal version scion-protocol-version)
      (equal scion-protocol-version 'ignore)
      (y-or-n-p 
       (format "Versions differ: %s (scion client) vs. %s (scion server). Continue? "
               scion-protocol-version version))
      (scion-net-close conn)
      (top-level)))

(defun scion-generate-connection-name (lisp-name)
  (loop for i from 1
        for name = lisp-name then (format "%s<%d>" lisp-name i)
        while (find name scion-net-processes 
                    :key #'scion-connection-name :test #'equal)
        finally (return name)))

(defun scion-connection-close-hook (process)
  (when (eq process scion-default-connection)
    (when scion-net-processes
      (scion-select-connection (car scion-net-processes))
      (message "Default connection closed; switched to #%S (%S)"
               (scion-connection-number)
               (scion-connection-name)))))

(add-hook 'scion-net-process-close-hooks 'scion-connection-close-hook)

;;;;; Commands on connections

(defun scion-disconnect ()
  "Disconnect all connections."
  (interactive)
  (mapc #'scion-net-close scion-net-processes))

(defun scion-connection-port (connection)
  "Return the remote port number of CONNECTION."
  (if (featurep 'xemacs)
      (car (process-id connection))
    (cadr (process-contact connection))))

(defun scion-process (&optional connection)
  "Return the Lisp process for CONNECTION (default `scion-connection').
Can return nil if there's no process object for the connection."
  nil
  ;; (let ((proc (scion-inferior-process connection)))
;;     (if (and proc 
;;              (memq (process-status proc) '(run stop)))
;;         proc))
  )

;; Non-macro version to keep the file byte-compilable. 
;; (defun scion-set-inferior-process (connection process)
;;   (setf (scion-inferior-process connection) process))

(defvar scion-inhibit-pipelining t
  "*If true, don't send background requests if Lisp is already busy.")

(defun scion-background-activities-enabled-p ()
  nil)


;;;; Communication protocol

;;;;; Emacs Lisp programming interface
;;;
;;; The programming interface for writing Emacs commands is based on
;;; remote procedure calls (RPCs). The basic operation is to ask Lisp
;;; to apply a named Lisp function to some arguments, then to do
;;; something with the result.
;;;
;;; Requests can be either synchronous (blocking) or asynchronous
;;; (with the result passed to a callback/continuation function).  If
;;; an error occurs during the request then the debugger is entered
;;; before the result arrives -- for synchronous evaluations this
;;; requires a recursive edit.
;;;
;;; You should use asynchronous evaluations (`scion-eval-async') for
;;; most things. Reserve synchronous evaluations (`scion-eval') for
;;; the cases where blocking Emacs is really appropriate (like
;;; completion) and that shouldn't trigger errors (e.g. not evaluate
;;; user-entered code).
;;;
;;; We have the concept of the "current Lisp package". RPC requests
;;; always say what package the user is making them from and the Lisp
;;; side binds that package to *BUFFER-PACKAGE* to use as it sees
;;; fit. The current package is defined as the buffer-local value of
;;; `scion-buffer-package' if set, and otherwise the package named by
;;; the nearest IN-PACKAGE as found by text search (first backwards,
;;; then forwards).
;;;
;;; Similarly we have the concept of the current thread, i.e. which
;;; thread in the Lisp process should handle the request. The current
;;; thread is determined solely by the buffer-local value of
;;; `scion-current-thread'. This is usually bound to t meaning "no
;;; particular thread", but can also be used to nominate a specific
;;; thread. The REPL and the debugger both use this feature to deal
;;; with specific threads.

(make-variable-buffer-local
 (defvar scion-current-thread t
   "The id of the current thread on the Lisp side.  
t means the \"current\" thread;
:repl-thread the thread that executes REPL requests;
fixnum a specific thread."))

(make-variable-buffer-local
 (defvar scion-buffer-package nil
   "The Lisp package associated with the current buffer.
This is set only in buffers bound to specific packages."))


(defun scion-current-package ()
  nil)

(defvar scion-accept-process-output-supports-floats 
  (ignore-errors (accept-process-output nil 0.0) t))

(defun scion-accept-process-output (&optional process timeout)
  "Like `accept-process-output' but the TIMEOUT argument can be a float."
  (cond (scion-accept-process-output-supports-floats
         (accept-process-output process timeout))
        (t
         (accept-process-output process 
                                (if timeout (truncate timeout))
                                ;; Emacs 21 uses microsecs; Emacs 22 millisecs
                                (if timeout (truncate (* timeout 1000000)))))))

;;; Synchronous requests are implemented in terms of asynchronous
;;; ones. We make an asynchronous request with a continuation function
;;; that `throw's its result up to a `catch' and then enter a loop of
;;; handling I/O until that happens.

(defvar scion-stack-eval-tags nil
  "List of stack-tags of continuations waiting on the stack.")

;;; `scion-rex' is the RPC primitive which is used to implement both
;;; `scion-eval' and `scion-eval-async'. You can use it directly if
;;; you need to, but the others are usually more convenient.

(defmacro* scion-rex ((&rest saved-vars)
                      (sexp &optional 
                            (package '(scion-current-package))
                            (thread 'scion-current-thread))
                      &rest continuations)
  "(scion-rex (VAR ...) (SEXP &optional PACKAGE THREAD) CLAUSES ...)

Remote EXecute SEXP.

VARs are a list of saved variables visible in the other forms.  Each
VAR is either a symbol or a list (VAR INIT-VALUE).

SEXP is evaluated and the printed version is sent to Lisp.

PACKAGE is evaluated and Lisp binds *BUFFER-PACKAGE* to this package.
The default value is (scion-current-package).

CLAUSES is a list of patterns with same syntax as
`destructure-case'.  The result of the evaluation of SEXP is
dispatched on CLAUSES.  The result is either a sexp of the
form (:ok VALUE) or (:abort).  CLAUSES is executed
asynchronously.

Note: don't use backquote syntax for SEXP, because Emacs20 cannot
deal with that."
  (let ((result (gensym))
	(gsexp (gensym)))
    `(lexical-let ,(loop for var in saved-vars
                         collect (etypecase var
                                   (symbol (list var var))
                                   (cons var)))
       (let ((,gsexp ,sexp))
	 (scion-dispatch-event 
	  (list :method (car ,gsexp)
		:params (cdr ,gsexp)
		:package ,package
		:continuation (lambda (,result)
				(destructure-case ,result
				  ,@continuations))))))))

(defun scion-eval (sexp &optional package)
  "Evaluate EXPR on the Scion server and return the result."
  (when (null package) (setq package (scion-current-package)))
  (let* ((tag (gensym (format "scion-result-%d-" 
                              (1+ (scion-continuation-counter)))))
	 (scion-stack-eval-tags (cons tag scion-stack-eval-tags)))
    (apply
     #'funcall 
     (catch tag
       (scion-rex (tag sexp)
           (sexp package)
         ((:ok value)
          (unless (member tag scion-stack-eval-tags)
            (error "Reply to canceled synchronous eval request tag=%S sexp=%S"
                   tag sexp))
          (throw tag (list #'identity value)))
	 ((:error msg)
	  (throw tag (list #'error (format "Scion Eval Error: %s" msg))))
         ((:abort)
          (throw tag (list #'error "Synchronous Remote Evaluation aborted"))))
       (let ((debug-on-quit t)
             (inhibit-quit nil)
             (conn (scion-connection)))
         (while t 
           (unless (eq (process-status conn) 'open)
             (error "Server connection closed unexpectedly"))
           (scion-accept-process-output nil 0.01)))))))

(defun scion-eval-async (sexp &optional cont package)
  "Evaluate EXPR on the server and call CONT with the result."
  (scion-rex (cont (buffer (current-buffer)))
	(sexp (or package (scion-current-package)))
    ((:ok result)
     (when cont
       (set-buffer buffer)
       (funcall cont result)))
    ((:error msg)
     (message "Scion Eval Async: %s" msg))
    ((:abort)
     (message "Evaluation aborted."))))

(put 'scion-eval-async 'lisp-indent-function 1)

;;;;; Protocol event handler (the guts)
;;;
;;; This is the protocol in all its glory. The input to this function
;;; is a protocol event that either originates within Emacs or arrived
;;; over the network from Lisp.
;;;
;;; Each event is a list beginning with a keyword and followed by
;;; arguments. The keyword identifies the type of event. Events
;;; originating from Emacs have names starting with :emacs- and events
;;; from Lisp don't.

(scion-def-connection-var scion-rex-continuations '()
  "List of (ID . FUNCTION) continuations waiting for RPC results.")

(scion-def-connection-var scion-continuation-counter 0
  "Continuation serial number counter.")

(defvar scion-event-hooks)

(defun scion-dispatch-event (event &optional process)
  (let ((scion-dispatching-connection (or process (scion-connection))))
    (or (run-hook-with-args-until-success 'scion-event-hooks event)
	(destructuring-bind (&key method error (result nil result-p) params id
				  continuation package
				  &allow-other-keys)
	    event
	  (cond
	   ((and method)
	    ;; we're trying to send a message
	    (when (and (scion-use-sigint-for-interrupt) (scion-busy-p))
	      (scion-display-oneliner "; pipelined request... %S" form))
	    (let ((id (incf (scion-continuation-counter))))
	      (push (cons id continuation) (scion-rex-continuations))
	      (scion-send `(:method ,method
			    :params ,params
			    :id ,id))))
	   ((and (or error result-p) id)
	    (let ((value nil))
	      (if error
		  (destructuring-bind (&key name message) error
		    (if (string= name "MalformedRequest")
			(progn
			  (scion-with-popup-buffer ("*Scion Error*")
			    (princ (format "Invalid protocol message:\n%s"
					   event))
			    (goto-char (point-min)))
			  (error "Invalid protocol message"))
		      (setq value (list :error message))))
		(setq value (list :ok result)))
	      
	      ;; we're receiving the result of a remote call
	      (let ((rec (assq id (scion-rex-continuations))))
		(cond (rec (setf (scion-rex-continuations)
				 (remove rec (scion-rex-continuations)))
			   (funcall (cdr rec) value))
		    (t
		     (error "Unexpected reply: %S %S" id value)))))))))))

(defun scion-send (sexp)
  "Send SEXP directly over the wire on the current connection."
  (scion-net-send sexp (scion-connection)))

(defun scion-stop-server ()
  "Stop the server we are currently connected to."
  (interactive)
  (scion-eval '(quit))
  (scion-disconnect))

(defun scion-use-sigint-for-interrupt (&optional connection)
  nil)

(defun scion-busy-p (&optional conn)
  "True if Haskell has outstanding requests.
Debugged requests are ignored."
  nil)

(defun scion-display-oneliner (format-string &rest format-args)
  (let* ((msg (apply #'format format-string format-args)))
    (unless (minibuffer-window-active-p (minibuffer-window))
      (message  "%s" (scion-oneliner msg)))))

(defun scion-oneliner (string)
  "Return STRING truncated to fit in a single echo-area line."
  (substring string 0 (min (length string)
                           (or (position ?\n string) most-positive-fixnum)
                           (1- (frame-width)))))

(defun scion-curry (fun &rest args)
  `(lambda (&rest more) (apply ',fun (append ',args more))))

(defun scion-rcurry (fun &rest args)
  `(lambda (&rest more) (apply ',fun (append more ',args))))

(defsubst scion-makehash (&optional test)
  (if (fboundp 'make-hash-table)
      (if test (make-hash-table :test test) (make-hash-table))
    (with-no-warnings
      (makehash test))))

;;;;; Snapshots of current Emacs state

;;; Window configurations do not save (and hence not restore)
;;; any narrowing that could be applied to a buffer.
;;;
;;; For this purpose, we introduce a superset of a window
;;; configuration that does include the necessary information to
;;; properly restore narrowing.
;;;
;;; We call this superset an Emacs Snapshot.

(defstruct (scion-narrowing-configuration
             (:conc-name scion-narrowing-configuration.))
  narrowedp beg end)

(defstruct (scion-emacs-snapshot (:conc-name scion-emacs-snapshot.))
  ;; We explicitly store the value of point even though it's implicitly
  ;; stored in the window-configuration because Emacs provides no
  ;; way to access the things stored in a window configuration.
  window-configuration narrowing-configuration point-marker)

(defun scion-current-narrowing-configuration (&optional buffer)
  (with-current-buffer (or buffer (current-buffer))
    (make-scion-narrowing-configuration :narrowedp (scion-buffer-narrowed-p)
                                        :beg (point-min-marker)
                                        :end (point-max-marker))))

(defun scion-set-narrowing-configuration (narrowing-cfg)
  (when (scion-narrowing-configuration.narrowedp narrowing-cfg)
    (narrow-to-region (scion-narrowing-configuration.beg narrowing-cfg)
                      (scion-narrowing-configuration.end narrowing-cfg))))

(defun scion-current-emacs-snapshot (&optional frame)
  "Returns a snapshot of the current state of FRAME, or the
currently active frame if FRAME is not given respectively."
  (with-current-buffer
      (if frame
          (window-buffer (frame-selected-window (selected-frame)))
          (current-buffer))
    (make-scion-emacs-snapshot
     :window-configuration    (current-window-configuration frame)
     :narrowing-configuration (scion-current-narrowing-configuration)
     :point-marker            (point-marker))))

(defun scion-set-emacs-snapshot (snapshot)
  "Restores the state of Emacs according to the information saved
in SNAPSHOT."
  (let ((window-cfg    (scion-emacs-snapshot.window-configuration snapshot))
        (narrowing-cfg (scion-emacs-snapshot.narrowing-configuration snapshot))
        (marker        (scion-emacs-snapshot.point-marker snapshot)))
    (set-window-configuration window-cfg) ; restores previously current buffer.
    (scion-set-narrowing-configuration narrowing-cfg)
    (goto-char (marker-position marker))))

(defun scion-current-emacs-snapshot-fingerprint (&optional frame)
  "Return a fingerprint of the current emacs snapshot.
Fingerprints are `equalp' if and only if they represent window
configurations that are very similar (same windows and buffers.)

Unlike real window-configuration objects, fingerprints are not
sensitive to the point moving and they can't be restored."
  (mapcar (lambda (window) (list window (window-buffer window)))
          (scion-frame-windows frame)))

(defun scion-frame-windows (&optional frame)
  "Return the list of windows in FRAME."
  (loop with last-window = (previous-window (frame-first-window frame))
        for window = (frame-first-window frame) then (next-window window)
        collect window
        until (eq window last-window)))

;;;;; Temporary popup buffers

(make-variable-buffer-local
 (defvar scion-popup-buffer-saved-emacs-snapshot nil
   "The snapshot of the current state in Emacs before the popup-buffer
was displayed, so that this state can be restored later on.
Buffer local in popup-buffers."))

(make-variable-buffer-local
 (defvar scion-popup-buffer-saved-fingerprint nil
   "The emacs snapshot \"fingerprint\" after displaying the buffer."))



(defun scion-popup-buffer (name buffer-vars)
  "Return a temporary buffer called NAME.
The buffer also uses the minor-mode `scion-popup-buffer-mode'.
Pressing `q' in the buffer will restore the window configuration
to the way it is when the buffer was created, i.e. when this
function was called."
  (when (and (get-buffer name) (kill-buffer (get-buffer name))))
  (with-current-buffer (get-buffer-create name)
    (set-syntax-table lisp-mode-syntax-table)
    (prog1 (pop-to-buffer (current-buffer))
      (scion-init-popup-buffer buffer-vars))))

(defun scion-init-popup-buffer (buffer-vars)
  (scion-popup-buffer-mode 1)
  (setq scion-popup-buffer-saved-fingerprint
        (scion-current-emacs-snapshot-fingerprint))
  (multiple-value-setq (scion-buffer-package 
                        scion-buffer-connection
                        scion-popup-buffer-saved-emacs-snapshot)
    buffer-vars))

(define-minor-mode scion-popup-buffer-mode 
  "Mode for displaying read only stuff"
  nil
  (" Scion-Tmp" scion-modeline-string)
  '(("q" . scion-popup-buffer-quit-function)
    ;("\C-c\C-z" . scion-switch-to-output-buffer)
    ;; ("\M-." . scion-edit-definition)
    ))

(make-variable-buffer-local
 (defvar scion-popup-buffer-quit-function 'scion-popup-buffer-quit
   "The function that is used to quit a temporary popup buffer."))

(defun scion-popup-buffer-quit-function (&optional kill-buffer-p)
  "Wrapper to invoke the value of `scion-popup-buffer-quit-function'."
  (interactive)
  (funcall scion-popup-buffer-quit-function kill-buffer-p))

;; Interface
(defun scion-popup-buffer-quit (&optional kill-buffer-p)
  "Get rid of the current (temp) buffer without asking.
Restore the window configuration unless it was changed since we
last activated the buffer."
  (interactive)
  (let ((buffer (current-buffer)))
    (when (scion-popup-buffer-snapshot-unchanged-p)
      (scion-popup-buffer-restore-snapshot))
    (with-current-buffer buffer
      (setq scion-popup-buffer-saved-emacs-snapshot nil) ; buffer-local var!
      (cond (kill-buffer-p (kill-buffer nil))
            (t (bury-buffer))))))

(defun scion-popup-buffer-snapshot-unchanged-p ()
  (equalp (scion-current-emacs-snapshot-fingerprint)
          scion-popup-buffer-saved-fingerprint))

(defun scion-popup-buffer-restore-snapshot ()
  (let ((snapshot scion-popup-buffer-saved-emacs-snapshot))
    (assert snapshot) 
    (scion-set-emacs-snapshot snapshot)))


;;;;; Event logging to *scion-events*
;;;
;;; The *scion-events* buffer logs all protocol messages for debugging
;;; purposes. Optionally you can enable outline-mode in that buffer,
;;; which is convenient but slows things down significantly.

(defvar scion-log-events t
  "*Log protocol events to the *scion-events* buffer.")

(defvar scion-outline-mode-in-events-buffer nil
  "*Non-nil means use outline-mode in *scion-events*.")

(defvar scion-event-buffer-name "*scion-events*"
  "The name of the scion event buffer.")

(defun scion-log-event (event)
  "Record the fact that EVENT occurred."
  (when scion-log-events
    (with-current-buffer (scion-events-buffer)
      ;; trim?
      (when (> (buffer-size) 100000)
        (goto-char (/ (buffer-size) 2))
        (re-search-forward "^(" nil t)
        (delete-region (point-min) (point)))
      (goto-char (point-max))
      (save-excursion
        (scion-pprint-event event (current-buffer)))
      (when (and (boundp 'outline-minor-mode)
                 outline-minor-mode)
        (hide-entry))
      (goto-char (point-max)))))

(defun scion-pprint-event (event buffer)
  "Pretty print EVENT in BUFFER with limited depth and width."
  (let ((print-length 20)
	(print-level 6)
	(pp-escape-newlines t))
    (pp event buffer)))

(defun scion-events-buffer ()
  (or (get-buffer scion-event-buffer-name)
      (let ((buffer (get-buffer-create scion-event-buffer-name)))
        (with-current-buffer buffer
          (buffer-disable-undo)
          (set (make-local-variable 'outline-regexp) "^(")
          (set (make-local-variable 'comment-start) ";")
          (set (make-local-variable 'comment-end) "")
          (when scion-outline-mode-in-events-buffer
            (outline-minor-mode)))
        buffer)))

;;;;; Buffer related

(defun scion-buffer-narrowed-p (&optional buffer)
  "Returns T if BUFFER (or the current buffer respectively) is narrowed."
  (with-current-buffer (or buffer (current-buffer))
    (let ((beg (point-min))
          (end (point-max))
          (total (buffer-size)))
      (or (/= beg 1) (/= end (1+ total))))))

(defun scion-column-max ()
  (save-excursion
    (goto-char (point-min))
    (loop for column = (prog2 (end-of-line) (current-column) (forward-line))
          until (= (point) (point-max))
          maximizing column)))

;;;---------------------------------------------------------------------------

;;;;; scion-mode-faces

(defgroup scion-mode-faces nil
  "Faces in scion-mode source code buffers."
  :prefix "scion-"
  :group 'scion-mode)

(defun scion-underline-color (color)
  "Return a legal value for the :underline face attribute based on COLOR."
  ;; In XEmacs the :underline attribute can only be a boolean.
  ;; In GNU it can be the name of a colour.
  (if (featurep 'xemacs)
      (if color t nil)
    color))

(defface scion-error-face
  `((((class color) (background light))
     (:underline ,(scion-underline-color "red")))
    (((class color) (background dark))
     (:underline ,(scion-underline-color "red")))
    (t (:underline t)))
  "Face for errors from the compiler."
  :group 'scion-mode-faces)

(defface scion-warning-face
  `((((class color) (background light))
     (:underline ,(scion-underline-color "orange")))
    (((class color) (background dark))
     (:underline ,(scion-underline-color "coral")))
    (t (:underline t)))
  "Face for warnings from the compiler."
  :group 'scion-mode-faces)

(defun scion-face-inheritance-possible-p ()
  "Return true if the :inherit face attribute is supported." 
  (assq :inherit custom-face-attributes))

(defface scion-highlight-face
  (if (scion-face-inheritance-possible-p)
      '((t (:inherit highlight :underline nil)))
    '((((class color) (background light))
       (:background "darkseagreen2"))
      (((class color) (background dark))
       (:background "darkolivegreen"))
      (t (:inverse-video t))))
  "Face for compiler notes while selected."
  :group 'scion-mode-faces)

;;;---------------------------------------------------------------------------
;;;; Overlays for compiler messages and other things

(defstruct (scion-compilation-result
             (:type list)
             (:conc-name scion-compilation-result.)
             (:constructor nil)
             (:copier nil))
  tag successp notes duration)


(defvar scion-project-root-dir nil
  "The root directory of the current project.

This is used, for example, to translate relative path names from
error messages into absolute path names.")

(defun scion-compiler-notes ()
  "Return all compiler notes, warnings, and errors."
  (scion-compilation-result.notes scion-last-compilation-result))

;;; TODO: notes should be sorted by filename (using a hashtable)

(defun scion-highlight-notes (notes &optional buffer)
  "Highlight compiler notes, warnings, and errors in the buffer."
  (interactive (list (scion-compiler-notes)))
  (with-temp-message (if (not buffer) "Highlighting notes..." nil)
    (save-excursion
      (save-restriction
        (widen)                  ; highlight notes on the whole buffer
        (scion-remove-old-overlays buffer)
	(let ((buffers (if buffer
			   (list buffer)
			   (scion-filter-buffers (lambda () scion-mode)))))
	  (loop for b in buffers do
		(with-current-buffer b
		  (save-excursion
		    (save-restriction
		      (widen)
		      (loop for note in (scion-notes-for-buffer notes b) do
			    (scion-overlay-note note b))))))))))
  nil)

(defun scion-notes-for-buffer (notes buffer)
  "Return only the notes that relate to BUFFER."
  (let ((fname (buffer-file-name buffer)))
    (if fname
	(gethash fname notes nil)
      nil)))

(defun scion-remove-old-overlays (&optional buffer)
  "Delete the existing Scion overlays in the current buffer."
  (dolist (buffer (if buffer
		      (list buffer)
		    (scion-filter-buffers (lambda () scion-mode))))
    (with-current-buffer buffer
      (save-excursion
        (save-restriction
          (widen)                ; remove overlays within the whole buffer.
          (goto-char (point-min))
          (while (not (eobp))
            (dolist (o (overlays-at (point)))
              (when (overlay-get o 'scion)
                (delete-overlay o)))
            (goto-char (next-overlay-change (point)))))))))

(defun scion-filter-buffers (predicate)
  "Return a list of buffers where PREDICATE returns true.
PREDICATE is executed in the buffer to test."
  (remove-if-not (lambda (%buffer)
                   (with-current-buffer %buffer
                     (funcall predicate)))
                 (buffer-list)))

(defun scion-flash-region (start end &optional timeout)
  (let ((overlay (make-overlay start end))) 
    (overlay-put overlay 'face 'secondary-selection)
    (run-with-timer (or timeout 0.2) nil 'delete-overlay overlay)))

;;; The node representation
;;;
;;; See Scion server JSON instances for details.

(defun scion-note.message (note)
  (plist-get note :message))

(defun scion-note.filename (note)
  (let ((loc (scion-note.location note)))
    (plist-get loc :file)))

(defun scion-note.line (note)
  (when-let (region (plist-get (scion-note.location note) :region))
    (destructuring-bind (sl sc el ec) region
      sl)))

(defun scion-note.col (note)
  (when-let (region (plist-get (scion-note.location note) :region))
    (destructuring-bind (sl sc el ec) region
      sc)))

(defun scion-note.region (note buffer)
  (when-let (region (plist-get (scion-note.location note) :region))
    (let ((filename (scion-note.filename note)))
      (when (equal (buffer-file-name buffer) filename)
	(destructuring-bind (sl sc el ec) region
	  (scion-location-to-region sl sc el ec buffer))))))

(defun scion-note.severity (note)
  (let ((k (plist-get note :kind)))
    (cond 
     ((string= k "warning") :warning)
     ((string= k "error") :error)
     (t :other))))

(defun scion-note.location (note)
  (plist-get note :location))

(defun scion-location-to-region (start-line start-col end-line end-col
				 &optional buffer)
  "Translate a Haskell (line,col) region into an Emacs region.

TODO: Fix up locations if buffer has been modified in between."
  (with-current-buffer (or buffer (current-buffer))
    (save-excursion
      (save-restriction
	(widen) 			; look in whole buffer
	(goto-char 1)
	(forward-line (1- start-line))
	(move-to-column start-col)
	(let ((start (point)))
	  (forward-line (- end-line start-line))
	  (move-to-column end-col)
	  (let ((end (point)))
	    (cond 
	     ((< end start)
	      (list end start))
	     ((= start end) ; span would be invisible
	      (list start (progn ; a bit of a hack, but well
			    (goto-char start)
			    (forward-word)
			    (point))))
	     (t
	      (list start end)))))))))

(defun scion-canonicalise-note-location (note)
  "Translate the note's location into absolute path names.
Modifies input note."
  ;; This should be done on the server now.
  note)

;;;;; Adding a single compiler note

(defun scion-overlay-note (note buffer)
  "Add a compiler note to the buffer as an overlay."
  (multiple-value-bind (start end) (scion-note.region note buffer)
    (when start
      (goto-char start)
      (let ((severity (scion-note.severity note))
            (message (scion-note.message note)))
        (scion-create-note-overlay note start end severity message)))))

(defun scion-create-note-overlay (note start end severity message)
  "Create an overlay representing a compiler note.
The overlay has several properties:
  FACE       - to underline the relevant text.
  SEVERITY   - for future reference, :NOTE, :STYLE-WARNING, :WARNING, or :ERROR.
  MOUSE-FACE - highlight the note when the mouse passes over.
  HELP-ECHO  - a string describing the note, both for future reference
               and for display as a tooltip (due to the special
               property name)."
  (let ((overlay (make-overlay start end)))
    (flet ((putp (name value) (overlay-put overlay name value)))
      (putp 'scion note)
      (putp 'face (scion-severity-face severity))
      ;(putp 'severity severity)
      (unless (scion-emacs-20-p)
	(putp 'mouse-face 'highlight))
      (putp 'help-echo message)
      overlay)))

(defun scion-severity-face (severity)
  "Return the name of the font-lock face representing SEVERITY."
  (ecase severity
    (:error         'scion-error-face)
    (:warning       'scion-warning-face)))

(defun scion-make-notes (notes0 &optional keep-existing-notes)
  (let ((notes (if keep-existing-notes
		   (scion-compiler-notes)
		 (scion-makehash #'equal))))
    (loop for note in notes0
	  do (progn
	       (scion-canonicalise-note-location note)
	       (let* ((fname (scion-note.filename note))
		      (old-notes (gethash fname notes)))
		 (puthash fname (cons note old-notes) notes))))
    notes))

(defun scion-next-note-in-buffer ()
  "Goto next note in current buffer."
  (interactive)
  (scion-next-note-in-buffer-aux nil))

(defun scion-previous-note-in-buffer ()
  "Goto previous note in current buffer if any."
  (interactive)
  (scion-next-note-in-buffer-aux t))

(defun scion-next-note-in-buffer-aux (&optional backwards)
  (flet ((my-next-overlay-change (p) (if backwards 
					 (previous-overlay-change p)
				       (next-overlay-change p)))
	 (my-eobp () (if backwards (bobp) (eobp))))
    (let ((note0 (scion-note-at-point)))
      (let ((next-note
	     (save-excursion
	       (block found-sth
		 (while (not (my-eobp))
		   (dolist (o (overlays-at (point)))
		     (let ((note (overlay-get o 'scion)))
		       (when (and note (not (equal note note0)))
			 (return-from found-sth (cons (point) note)))))
		   (goto-char (my-next-overlay-change (point))))))))
	(if next-note
	    (progn
	      (goto-char (car next-note))
	      (message "%s" (scion-note.message (cdr next-note))))
	  (message "No more notes in this buffer."))))))

(defun scion-note-at-point (&optional pt)
  (block nil
    (let ((pt (or pt (point))))
      (dolist (o (overlays-at pt))
	(let ((note (overlay-get o 'scion)))
	  (when note
	    (return note)))))))

;;;---------------------------------------------------------------------------
;;; The buffer that shows the compiler notes

(defvar scion-compiler-notes-mode-map)

(define-derived-mode scion-compiler-notes-mode fundamental-mode 
  "Compiler-Notes"
  "\\<scion-compiler-notes-mode-map>\
\\{scion-compiler-notes-mode-map}
\\{scion-popup-buffer-mode-map}
"
  ;(scion-set-truncate-lines)
  )

(scion-define-keys scion-compiler-notes-mode-map
  ((kbd "RET") 'scion-compiler-notes-default-action-or-show-details)
  ([return] 'scion-compiler-notes-default-action-or-show-details)
  ([mouse-2] 'scion-compiler-notes-default-action-or-show-details/mouse)
  ((kbd "q") 'scion-popup-buffer-quit-function))

(defun scion-compiler-notes-default-action-or-show-details/mouse (event)
  "Invoke the action pointed at by the mouse, or show details."
  (interactive "e")
  (destructuring-bind (mouse-2 (w pos &rest _) &rest __) event
    (save-excursion
      (goto-char pos)
      (let ((fn (get-text-property (point) 
                                   'scion-compiler-notes-default-action)))
	(if fn (funcall fn) (scion-compiler-notes-show-details))))))

(defun scion-compiler-notes-default-action-or-show-details ()
  "Invoke the action at point, or show details."
  (interactive)
  (let ((fn (get-text-property (point) 'scion-compiler-notes-default-action)))
    (if fn (funcall fn) (scion-compiler-notes-show-details))))

(defun scion-compiler-notes-show-details ()
  (interactive)
  (let* ((tree (scion-tree-at-point))
         (note (plist-get (scion-tree.plist tree) 'note))
         (inhibit-read-only t))
    (cond ((not (scion-tree-leaf-p tree))
           (scion-tree-toggle tree))
          (t
           (scion-show-source-location note t)))))

(defun scion-show-source-location (note &optional no-highlight-p)
  (save-selected-window   ; show the location, but don't hijack focus.
    (scion-goto-source-location note)
    ;(unless no-highlight-p (sldb-highlight-sexp))
    ;(scion-show-buffer-position (point))
    ))

(defun scion-goto-source-location (note)
  (let ((file (scion-note.filename note)))
    (when file
      (let ((buff (find-buffer-visiting file)))
	(if buff
	    (let ((buff-window (get-buffer-window buff)))
	      (if buff-window
		  (select-window buff-window)
		(display-buffer buff)))
	  (progn
	    (find-file-other-window file)
	    (setq buff (find-buffer-visiting file))))
	(goto-line (scion-note.line note))
	(move-to-column (scion-note.col note))
	(let ((r (scion-note.region note buff)))
	  (with-current-buffer buff
	    (scion-flash-region (car r) (cadr r) 0.5)))))))

(defun scion-list-compiler-notes (notes &optional no-popup)
  "Show the compiler notes NOTES in tree view.

If NO-POPUP is non-NIL, only show the buffer if it is already visible."
  (interactive (list (scion-compiler-notes)))
  (labels ((fill-out-buffer ()
	      (erase-buffer)
	      (scion-compiler-notes-mode)
	      (when (null notes)
		(insert "[no notes]"))
	      (let ((collapsed-p))
		(dolist (tree (scion-compiler-notes-to-tree notes))
		  (when (scion-tree.collapsed-p tree) (setf collapsed-p t))
		  (scion-tree-insert tree "")
		  (insert "\n"))
		(goto-char (point-min)))))
    (with-temp-message "Preparing compiler note tree..."
      (if no-popup
	  (with-current-buffer (get-buffer-create "*SCION Compiler-Notes*")
	    (setq buffer-read-only nil)
	    (fill-out-buffer)
	    (setq buffer-read-only t))
	(scion-with-popup-buffer ("*SCION Compiler-Notes*")
	  (fill-out-buffer))))))

(defvar scion-tree-printer 'scion-tree-default-printer)

(defun scion-compiler-notes-to-tree (notes)
  (let ((warns nil)
	(errs nil))
    (maphash (lambda (file notes)
	       (loop for note in notes
		     do (case (scion-note.severity note)
			  (:warning (setq warns (cons note warns)))
			  (:error (setq errs (cons note errs))))))
	     notes)
    (let ((alist (list (cons :error errs)
		       (cons :warning warns))))
      (loop for (severity . sev-notes) in alist
	    collect (scion-tree-for-severity severity sev-notes nil)))))

(defun scion-tree-for-severity (severity notes collapsed-p)
  (make-scion-tree :item (format "%s (%d)"
				 (case severity
				   (:warning "Warnings")
				   (:error "Errors")
				   (t (print severity)))
				 (length notes))
		   :kids (mapcar #'scion-tree-for-note notes)
		   :collapsed-p collapsed-p))

(defun scion-tree-for-note (note)
  (make-scion-tree :item (format "%s:\n%s"
				 (scion-note.filename note)
				 (scion-note.message note))
		   :plist (list 'note note)
		   :print-fn scion-tree-printer))


;;;---------------------------------------------------------------------------

(defmacro* scion-handling-failure ((res-var) &body body)
  (let ((x (gensym))
	(val (gensym)))
  `(lambda (,x)
     (destructure-case ,x
       ((:ok ,val)
	(let ((,res-var ,val))
	  ,@body))
       ((:error ,val)
	(message "Remote command failed: %s" ,val)
	nil)))))

(put 'scion-handling-failure 'lisp-indent-function 1)

(defun scion-cabal-root-dir (&optional start-directory)
  "Look for a <name>.cabal file from START-DIRECTORY upwards."
  (let ((dir (or start-directory
		 default-directory
		 (error "No start directory given"))))
    (if (car (directory-files dir t ".+\.cabal$"))
	dir
      (let ((next-dir (file-name-directory (directory-file-name
                                            (file-truename dir)))))
	(unless (or (equal dir next-dir) (null next-dir))
          (scion-cabal-root-dir next-dir))))))

(defun scion-cabal-file (dir)
  "Return the only Cabal file in the given directory.
Returns NIL if the directory does not contain such file, and
signals an error if multiple files are present."
  (let ((cabal-files (directory-files dir t ".+\.cabal$")))
    (if (car cabal-files)
	(if (cadr cabal-files)
	    (error "Multiple .cabal files in directory: %s" dir)
	  (car cabal-files))
      nil)))

(defun scion-open-cabal-project (root-dir rel-dist-dir extra-args)
  "Load project metadata from a Cabal description.  

This does not load the project but merely loads the metadata.

ROOT-DIR is the project root directory \(the directory
which contains the .cabal file\).

REL-DIST-DIR is the directory name relative to the project root.
By default Scion uses \".scion-dist\" to avoid interfering with
command line tools.

EXTRA-ARGS is a string of command line flags."
  (interactive (scion-interactive-configure-args))
  (lexical-let ((root-dir root-dir))
    (scion-eval-async `(open-cabal-project :root-dir ,(expand-file-name root-dir)
					   :dist-dir ,rel-dist-dir
					   :extra-args ,(split-string extra-args))
		      (lambda (x)
			(setq scion-project-root-dir root-dir)
			(message (format "Cabal project loaded: %s" x)))))
  (message "Loading Cabal project."))

(defun scion-interactive-configure-args ()
  (let ((root (scion-cabal-root-dir)))
     (list (funcall (if (fboundp 'read-directory-name)
                        'read-directory-name
                      'read-file-name)
		    "Directory: " root root)
	   (read-from-minibuffer "Dist directory: " ".dist-scion")
	   (read-from-minibuffer "Configure Flags: " ""))))

(defun scion-configure-cabal-project (root-dir rel-dist-dir extra-args)
  "Configure/Reconfigure a Cabal project.  

This does not load the project but merely loads the metadata and
pre-processes files.

ROOT-DIR is the project root directory \(the directory
which contains the .cabal file\).

REL-DIST-DIR is the directory name relative to the project root.
By default Scion uses \".scion-dist\" to avoid interfering with
command line tools.

EXTRA-ARGS is a string of command line flags."
  (interactive (scion-interactive-configure-args))
  (lexical-let ((root-dir root-dir))
    (scion-eval-async `(configure-cabal-project :root-dir ,(expand-file-name root-dir)
						:dist-dir ,rel-dist-dir
						:extra-args ,(split-string extra-args))
      (lambda (x)
	(setq scion-project-root-dir root-dir)
	(message (format "Cabal project loaded: %s" x))))))

(defun scion-count-notes (notes)
  (let ((warns 0)
	(errs 0))
    (loop for n in notes 
	  when (eq (scion-note.severity n) :warning) do (incf warns)
	  when (eq (scion-note.severity n) :error) do (incf errs))
    (list warns errs)))


(defun scion-report-compilation-result (result &optional buf)
  (destructuring-bind (&key succeeded notes duration) result
    (let ((tag 'compilation-result)
	  (successp (if (eq succeeded json-false) nil t)))
      (multiple-value-bind (nwarnings nerrors)
	  (scion-count-notes notes)
	(let ((notes (scion-make-notes notes)))
	  (setq scion-last-compilation-result
		(list tag successp notes duration))
	  (scion-highlight-notes notes buf)
	  (if (not buf)
	      (progn
		(scion-show-note-counts successp nwarnings nerrors duration)
		(when (< 0 (+ nwarnings nerrors))
		  (scion-list-compiler-notes notes)))
	    (scion-update-compilater-notes-buffer))
	  (scion-report-status (format ":%d/%d" nerrors nwarnings))
	  nil)))))

(defun scion-update-compilater-notes-buffer ()
  "Update the contents of the compilation notes buffer if it is open somewhere."
  (interactive)
  ;; XXX: background typechecking currently does not keep notes from
  ;; other files
  (when (get-buffer "*SCION Compiler-Notes*")
    (scion-list-compiler-notes (scion-compiler-notes) t)))
    
;;     ((:ok warns)
;;      (setq scion-last-compilation-result
;; 	   (list 42 (mapc #'scion-canonicalise-note-location
;; 			  warns) t nil))
;;      (scion-highlight-notes warns)
;;      (scion-show-note-counts t warns nil))
;;     ((:error errs warns)
;;      (let ((notes (mapc #'scion-canonicalise-note-location
;; 			(append errs warns))))
;;        (setq scion-last-compilation-result
;; 	     (list 42 notes nil nil))
;;        (scion-highlight-notes notes))
;;      (scion-show-note-counts nil warns errs))))

(defun scion-show-note-counts (successp nwarnings nerrors secs)
  (message "Compilation %s: %s%s%s"
	   (if successp "finished" "FAILED")
	   (scion-note-count-string "error" nerrors)
	   (scion-note-count-string "warning" nwarnings)
	   (if secs (format "[%.2f secs]" secs) "")))

(defun scion-note-count-string (category count &optional suppress-if-zero)
  (cond ((and (zerop count) suppress-if-zero)
         "")
        (t (format "%2d %s%s " count category (if (= count 1) "" "s")))))

(defun scion-supported-languages ()
  ;; TODO: cache result
  (scion-eval '(list-supported-languages)))

(defun haskell-insert-language (lang)
  "Insert a LANGUAGE pragma at the top of the file."
  ;; TODO: automatically jump to or insert LANGUAGE pragma
  (interactive
   (let ((langs (scion-supported-languages)))
     (list (scion-completing-read "Language: " langs))))
  (save-excursion
    (goto-char (point-min))
    (insert "{-# LANGUAGE " lang " #-}\n"))
  (message "Added language %s" lang))

(defun scion-supported-pragmas ()
  ;; TODO: cache result
  (scion-eval '(list-supported-pragmas)))

(defun haskell-insert-pragma (pragma)
  "Insert a pragma at the current point."
  (interactive (let ((choices (scion-supported-pragmas)))
		 ;; standard completing-read cannot even deal properly
		 ;; with upper-case words.
		 (list (scion-completing-read "Pragma: " choices))))
  (insert "{-# " (upcase pragma) "  #-}")
  (backward-char 4))

(defun scion-supported-flags ()
  ;; TODO: cache result
  (scion-eval '(list-supported-flags)))

(defun haskell-insert-flag (flag)
  "Insert a command line flag at the curretn point."
  ;; TODO: automatically insert/add OPTIONS pragma
  (interactive
   (let ((flags (scion-supported-flags)))
     (list (scion-completing-read "Flag: " flags))))
  (insert flag))

(defun scion-set-command-line-flag (flag)
  (interactive "sCommand Line Flag: ")
  (scion-eval `(add-command-line-flag :flag ,flag)))

(defun scion-exposed-modules ()
  (scion-eval '(list-exposed-modules)))

(defun haskell-insert-module-name (mod)
  "Insert a module name at the current point.

When called interactively tries to complete to modules of all
installed packages (However, not of the current project.)"
  (interactive 
   (let ((mods (scion-exposed-modules)))
     (list (scion-completing-read "Module: " mods))))
  (insert mod))

(define-key scion-mode-map "\C-cil" 'haskell-insert-language)
(define-key scion-mode-map "\C-cip" 'haskell-insert-pragma)
(define-key scion-mode-map "\C-cif" 'haskell-insert-flag)
(define-key scion-mode-map "\C-cim" 'haskell-insert-module-name)

(define-key scion-mode-map "\C-c\C-o" 'scion-open-cabal-project)
(define-key scion-mode-map "\C-c\C-x\C-l" 'scion-load)
(define-key scion-mode-map "\M-n" 'scion-next-note-in-buffer)
(define-key scion-mode-map "\M-p" 'scion-previous-note-in-buffer)
(define-key scion-mode-map "\C-c\C-n" 'scion-list-compiler-notes)
(define-key scion-mode-map [(control ?c) (control ?\.)] 'scion-goto-definition)

(defun haskell-insert-module-header (module-name &optional
						 author
						 email)
  (interactive (list (read-from-minibuffer "Module name: ")
		     (read-from-minibuffer "Author name: " user-full-name)
		     (read-from-minibuffer "Author email: " user-mail-address)))
  (insert "-- |"
          "\n-- Module      : " module-name
	  "\n-- Copyright   : (c) " author " " (substring (current-time-string) -4)
	  "\n-- License     : BSD-style\n--" ;; TODO: extract from .cabal file
	  "\n-- Maintainer  : " email
	  "\n-- Stability   : experimental"
	  "\n-- Portability : portable\n--\n"))

(defun scion-set-ghc-verbosity (n)
  (interactive "nLevel [0-5]: ")
  (scion-eval `(set-ghc-verbosity :level ,n)))

;;;---------------------------------------------------------------------------

(defun scion-emacs-20-p ()
  (and (not (featurep 'xemacs))
       (= emacs-major-version 20)))

;;;---------------------------------------------------------------------------

(defalias 'scion-float-time
  (if (fboundp 'float-time)
      'float-time
    (if (featurep 'xemacs)
	(lambda ()
	  (multiple-value-bind (s0 s1 s2) (current-time)
	    (+ (* (float (ash 1 16)) s0) (float s1) (* 0.0000001 s2)))))))

;;;---------------------------------------------------------------------------
;;;; Flycheck (background type checking)

(make-variable-buffer-local 
 (defvar scion-flycheck-timer nil
   "The timer for starting background compilation"))

(make-variable-buffer-local
;; TODO: hm, maybe this should be global (due to single-threadedness)
(defvar scion-flycheck-is-running nil
  "If t, the (single-threaded) background typechecker is running."))

(make-variable-buffer-local
 (defvar scion-flycheck-last-change-time nil
   "Time of last buffer change."))

(defcustom scion-flycheck-no-changes-timeout 2.0
  "Time to wait after last change before starting compilation."
  :group 'scion
  :type 'number)

(defun scion-turn-on-flycheck ()
  "Turn on flycheck in current buffer"
  (interactive)
  (if (not scion-mode)
      (message "Background typechecking only supported inside scion-mode.")
    (add-hook 'after-change-functions 'scion-flycheck-after-change-function nil t)
    (add-hook 'kill-buffer-hook 'scion-kill-buffer-hook nil t)

    (scion-flycheck-on-save 1)

    ;; TODO: update modeline

    (setq scion-flycheck-timer
	  (run-at-time nil 1 'scion-flycheck-on-timer-event (current-buffer)))))

(defun scion-turn-off-flycheck ()
  (interactive)

  (remove-hook 'after-change-functions 'scion-flycheck-after-change-function t)
  (remove-hook 'kill-buffer-hook 'scion-kill-buffer-hook t)

  (scion-flycheck-on-save -1)
  ;; TODO: delete overlays?
  (when scion-flycheck-timer
    (cancel-timer scion-flycheck-timer)
    (setq scion-flycheck-timer nil))
  (setq scion-flycheck-is-running nil))

(make-variable-buffer-local
 (defvar scion-flycheck-on-save-state nil
   "Non-nil iff type checking should be performed when the file is saved."))

(defun scion-flycheck-on-save (&optional arg)
  "Toggle type checking the current file when it is saved.

A positive argument forces type checking to be on, a negative
forces it to be off.  NIL toggles the current state."
  (interactive "P")
  (if (not scion-mode)
      (message "Background typechecking only supported inside scion-mode.")
    (let ((new-state 
	   (cond
	    ((null arg) (not scion-flycheck-on-save-state))
	    ((consp arg) nil)
	    ((numberp arg) (>= arg 0)))))
      (when (not (eq (not new-state)
		     (not scion-flycheck-on-save-state)))
	(if new-state
	    (add-hook 'after-save-hook 'scion-after-save-hook nil t)
	  (remove-hook 'after-save-hook 'scion-after-save-hook t))
      
	(setq scion-flycheck-on-save-state new-state)
	(message (format "Typecheck-on-save has been turned %s"
			 (if new-state "ON" "OFF")))))))

(defun scion-flycheck-after-change-function (start stop len)
  ;; TODO: be more smarter about which parts need updating.
  ;;
  ;; flymake (optionally) supports syntax/typechecking if a newline was inserted
  (setq scion-flycheck-last-change-time (scion-float-time)))

(defun scion-after-save-hook ()
  (when (and scion-mode
	     (not scion-flycheck-is-running))
    (setq scion-flycheck-last-change-time nil)
    (scion-flycheck-start-check)))
 
(defun scion-kill-buffer-hook ()
  (when scion-flycheck-timer
    (cancel-timer scion-flycheck-timer)
    (setq scion-flycheck-timer nil)))

(defun scion-flycheck-on-timer-event (buffer)
  "Start a syntax check for buffer BUFFER if necessary."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (when (and (not scion-flycheck-is-running)
		 scion-flycheck-last-change-time
		 (> (- (scion-float-time) scion-flycheck-last-change-time)
                    scion-flycheck-no-changes-timeout))
	(setq scion-flycheck-last-change-time nil)
	;; HACK: prevent scion-after-save-hook from running a typecheck
	(setq scion-flycheck-is-running t)
	(save-buffer buffer)
	(scion-flycheck-start-check)))))

(defun scion-flycheck-start-check ()
  (interactive)
  (when (scion-connected-p)
    (let ((filename (buffer-file-name)))
      (setq scion-flycheck-is-running t)
      (scion-report-status ":-/-")
      (scion-eval-async `(background-typecheck-file :file ,filename)
	 (lambda (result)
	   (setq scion-flycheck-is-running nil)
	   (destructuring-bind (ok comp-rslt) result
	     (if (eq ok :Right)
		 (scion-report-compilation-result comp-rslt
						  (current-buffer))
	       (scion-report-status "[?]")
	       (message comp-rslt)))
	   nil)))))

(make-variable-buffer-local
 (defvar scion-mode-line-notes nil))

(defun scion-report-status (status)
  (let ((stats-str (concat " Scion" status)))
    (setq scion-mode-line stats-str)
    (force-mode-line-update)))

;;;---------------------------------------------------------------------------
;;;; To be sorted

(defun scion-thing-at-point ()
  (interactive)
  (let ((filename (buffer-file-name))
	(line (line-number-at-pos))
	(col (current-column)))
    (message 
     (let ((rslt (scion-eval `(thing-at-point :file ,filename 
					      :line ,line 
					      :column ,col))))
       (funcall (lambda (r) (format "%s" (cadr r))) rslt)))))

(defun scion-dump-sources ()
  (interactive)
  (scion-eval '(dump-sources)))

(defun scion-dump-defined-names ()
  (interactive)
  (scion-eval '(dump-defined-names)))

(defun scion-dump-module-graph ()
  (interactive)
  (scion-eval '(dump-module-graph)))

(defun scion-dump-name-db ()
  (interactive)
  (scion-eval '(dump-name-db)))

(define-key scion-mode-map "\C-c\C-t" 'scion-thing-at-point)

(provide 'scion)

(defun scion-load (comp)
  "Load current file or Cabal project.

If the file is within a Cabal project, prompts the user which
component to load, or whether only the current file should be
loaded."
  (interactive (list (scion-select-component)))
  (cond 
   ((null comp)
    (error "Invalid component"))
   (t
    (scion-load-component% comp))))

(defun scion-load-component% (comp)
  (message "Loading %s..." (scion-format-component comp))
  (scion-eval-async `(load :component ,comp)
    (lambda (result)
      (scion-report-compilation-result result))))

(defun scion-cabal-component-p (comp)
  (cond
   ((plist-member comp :library)
    t)
   ((plist-member comp :executable)
    t)
   (t
    nil)))

(defun scion-select-component ()
  (let* ((cabal-dir (scion-cabal-root-dir))
	 (cabal-file (ignore-errors (scion-cabal-file cabal-dir)))
	 (cabal-components 
          (when cabal-file 
            (ignore-errors (scion-cabal-components cabal-file))))
	 (options (nconc cabal-components
			 `((:file ,(buffer-file-name))))))
    (if (null (cdr options))
	(car options)
      ;; TODO: abstract this kludge into `scion-completing-read`
      (let* ((disp->comp (scion-makehash #'equal))
	     (opts (loop for c in options 
			 do (puthash (scion-format-component c) c disp->comp)
			 collect (scion-format-component c))))
	(gethash (scion-completing-read "Load Component: "
					opts
					nil
					t)
		 disp->comp)))))

(defun scion-format-component (comp)
  (cond
   ((plist-member comp :library)
    "Library")
   ((plist-member comp :executable)
    (format "Executable %s" (plist-get comp :executable)))
   ((plist-member comp :file)
    (format "File %s" (plist-get comp :file)))
   (t
    (format "%s" comp))))


(defun scion-cabal-components (cabal-file)
  "Return list of components in CABAL-FILE.
The result is a list where each element is either the symbol
LIBRARY or (EXECUTABLE <name>)."
  (let ((comps (scion-eval `(list-cabal-components :cabal-file ,cabal-file))))
    comps))

(defun scion-get-verbosity ()
  "Return the verbosity of the Scion server."
  (interactive)
  (scion-eval '(get-verbosity)))

(defun scion-set-verbosity (v)
  (interactive "nVerbosity[0-3]: ")
  (scion-eval `(set-verbosity :level ,v)))

(defun scion-defined-names ()
  (scion-eval '(defined-names)))

(defun scion-ident-at-point ()
  ;; TODO: recognise proper haskell symbols
  (let ((s (thing-at-point 'symbol)))
    (if s 
	(substring-no-properties s)
      nil)))

(defun scion-goto-definition (name)
  (interactive 
   (let ((names (scion-defined-names))
	 (dflt (scion-ident-at-point)))
     (if (find dflt names :test #'string=)
	 (list dflt)
       (list (scion-completing-read "Goto Definition: " names nil nil dflt)))))
  (let ((sites (scion-eval `(name-definitions :name ,name))))
    (if (not sites)
	(message "No definition site known")
      (let* ((loc (car sites)) ;; XXX: deal with multiple locations
	     (dummy-note (list :kind "warning" :location loc :message "definition")))
	(scion-goto-source-location dummy-note)))))

;; Local Variables: 
;; outline-regexp: ";;;;+"
;; End:
;; indent-tabs-mode: nil
