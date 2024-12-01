use std::time::{Duration, Instant};
use advent_2024::terminal::{Color, Terminal, TerminalImage, TerminalRender};

fn main() {
    let _drop = Terminal::init();

    let args = std::env::args().skip(1).collect::<Vec<_>>();
    match args.first() {
        Some(name) => {
            match name.as_str() {
                "expand" => expand(&args[1..]),
                "image" => image(),
                "one_line" => one_line(),
                _ => panic!("Unknown: {}", name),
            }
        }
        None => demo(),
    }

    fn demo() {
        expand(&[]);
        image();
        one_line();
    }

    fn expand(args: &[String]) {
        let n = args.first().map(|a| a.parse().expect("Invalid num")).unwrap_or(50);
        for i in (0..=n).chain((0..n).rev()) {
            let start = Instant::now();
            let mut print = i.to_string();
            print.push('\n');
            for _ in 0..i {
                let c = format!("{}", if i%2 == 0 {'*'} else {'#'});
                print.push_str(&c.repeat(i));
                print.push('\n');
            }
            Terminal::interactive_display(print, start + Duration::from_millis(200));
        }
    }

    fn image() {
        static COLORS: [Color; 7] = [Color::RED, Color::ORANGE, Color::YELLOW, Color::GREEN, Color::CYAN, Color::BLUE, Color::MAGENTA];
        struct Rainbow {
            offset: usize,
        }
        impl TerminalRender for Rainbow {
            fn render(&self, _w: usize, _h: usize) -> TerminalImage {
                let width = 20;
                let mut pixels = Vec::new();
                for i in 0..(width-1) { // Notice the image an odd number of pixels tall
                    for j in 0..width {
                        let idx = 100 - i - j + self.offset;
                        // stretch each pixel 2-wide (and adjust width below) to demo deduping codes
                        pixels.push(COLORS[idx % COLORS.len()]);
                        pixels.push(COLORS[idx % COLORS.len()]);
                    }
                }
                TerminalImage{ pixels, width: width*2, }
            }
        }

        for offset in 0..100 {
            let start = Instant::now();
            Terminal::interactive_render(&Rainbow{offset}, start + Duration::from_millis(100));
        }
    }

    fn one_line() {
        for i in (0..=200).rev() {
            let start = Instant::now();
            Terminal::interactive_display(i, start + Duration::from_millis(20));
        }
        std::thread::sleep(Duration::from_secs(1));
        println!("Final Message");
    }
}
