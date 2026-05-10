use std::io::{self, Write};

use colored::{Color, Colorize as _};

pub struct Logger {
    quiet: bool,
}

impl Logger {
    pub fn new(quiet: bool) -> Self {
        Self { quiet }
    }

    pub fn log(&self, title: impl ToString, text: impl ToString) -> io::Result<()> {
        self.log_internal(io::stdout(), title, text, Color::Green, false)
    }

    pub fn elog(&self, title: impl ToString, text: impl ToString) -> io::Result<()> {
        self.log_internal(io::stderr(), title, text, Color::Red, true)
    }

    fn log_internal(
        &self,
        stream: impl Write,
        title: impl ToString,
        text: impl ToString,
        title_color: Color,
        ignore_quiet: bool,
    ) -> io::Result<()> {
        if !ignore_quiet && self.quiet {
            return Ok(());
        }

        self.log_core(stream, title.to_string(), text.to_string(), title_color)
    }

    fn log_core(
        &self,
        mut stream: impl Write,
        title: String,
        text: String,
        title_color: Color,
    ) -> io::Result<()> {
        write!(
            stream,
            "{}",
            format!("{title:>12}").color(title_color).bold()
        )?;

        let mut lines = text.lines();

        if let Some(line) = lines.next() {
            writeln!(stream, " {line}")?;
        }

        for line in lines {
            write!(stream, "{:>13}", ' ')?;
            writeln!(stream, "{line}")?;
        }

        Ok(())
    }
}

#[macro_export]
macro_rules! log {
    ($logger:expr, $title:expr $(,)?) => {
        $crate::log!($logger, $title, "")
    };

    ($logger:expr, $title:expr, $format:literal) => {
        $crate::log!($logger, $title, $format,)
    };

    ($logger:expr, $title:expr, $format:literal, $($arg:tt)*) => {
        $logger.log($title, format!($format, $($arg)*))
    };
}

#[macro_export]
macro_rules! elog {
    ($logger:expr, $title:expr $(,)?) => {
        $crate::elog!($logger, $title, "")
    };

    ($logger:expr, $title:expr, $format:literal) => {
        $crate::elog!($logger, $title, $format,)
    };

    ($logger:expr, $title:expr, $format:literal, $($arg:tt)*) => {
        $logger.elog($title, format!($format, $($arg)*))
    };
}
