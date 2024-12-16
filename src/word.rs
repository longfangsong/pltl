use std::collections::HashSet;

use crate::pltl::PLTL;

pub type Word = fn(usize) -> HashSet<String>;

macro_rules! gen_word {
    ($w:ident, $($t:expr => [$($atom:ident),*]),*) => {
        pub fn $w(time: usize) -> HashSet<String> {
            let mut map = std::collections::HashMap::new();
            $(
                #[allow(unused_mut)]
                let mut set = HashSet::new();
                $(
                    set.insert(String::from(stringify!($atom)));
                )*
                map.insert($t, set);
            )*
            map.get(&time).cloned().unwrap_or_default()
        }
    };
}

pub(crate) use gen_word;

pub struct WordAtTime {
    pub word: Word,
    pub time: usize,
}

const MAX_DETECT_COUNT: usize = 10000;

impl WordAtTime {
    pub fn models(&self, ltl: &PLTL) -> bool {
        match ltl {
            PLTL::Top => true,
            PLTL::Bottom => false,
            PLTL::Atom(atom) => {
                let word = self.word;
                word(self.time).contains(atom)
            }
            PLTL::Not(pltl) => !self.models(pltl),
            PLTL::And(lhs, rhs) => self.models(lhs) && self.models(rhs),
            PLTL::Or(lhs, rhs) => self.models(lhs) || self.models(rhs),
            PLTL::Next(box pltl) => WordAtTime {
                word: self.word,
                time: self.time + 1,
            }
            .models(pltl),
            PLTL::Until(lhs, rhs) => {
                'loop_r: for r in self.time..=MAX_DETECT_COUNT {
                    let at_r = WordAtTime {
                        word: self.word,
                        time: r,
                    };
                    if at_r.models(rhs) {
                        for s in self.time..r {
                            let at_s = WordAtTime {
                                word: self.word,
                                time: s,
                            };
                            if !at_s.models(lhs) {
                                continue 'loop_r;
                            }
                        }
                        return true;
                    }
                }
                false
            }
            PLTL::Yesterday(pltl) => {
                if self.time == 0 {
                    false
                } else {
                    WordAtTime {
                        word: self.word,
                        time: self.time - 1,
                    }
                    .models(pltl)
                }
            }
            PLTL::Since(lhs, rhs) => {
                'loop_r: for r in 0..=self.time {
                    let at_r = WordAtTime {
                        word: self.word,
                        time: r,
                    };
                    if at_r.models(rhs) {
                        for s in r + 1..=self.time {
                            let at_s = WordAtTime {
                                word: self.word,
                                time: s,
                            };
                            if !at_s.models(lhs) {
                                continue 'loop_r;
                            }
                        }
                        return true;
                    }
                }
                false
            }
            PLTL::Eventually(pltl) => self.models(&PLTL::Until(Box::new(PLTL::Top), pltl.clone())),
            PLTL::Once(pltl) => self.models(&PLTL::Since(Box::new(PLTL::Top), pltl.clone())),
            PLTL::Globally(pltl) => self.models(&PLTL::Not(Box::new(PLTL::Eventually(Box::new(
                PLTL::Not(pltl.clone()),
            ))))),
            PLTL::Historically(pltl) => self.models(&PLTL::Not(Box::new(PLTL::Once(Box::new(
                PLTL::Not(pltl.clone()),
            ))))),
            PLTL::MightyRelease(lhs, rhs) => self.models(&PLTL::Until(
                rhs.clone(),
                Box::new(PLTL::And(lhs.clone(), rhs.clone())),
            )),
            PLTL::Before(lhs, rhs) => self.models(&PLTL::Since(
                rhs.clone(),
                Box::new(PLTL::And(lhs.clone(), rhs.clone())),
            )),
            PLTL::WeakUntil(lhs, rhs) => self.models(&PLTL::Or(
                Box::new(PLTL::Until(lhs.clone(), rhs.clone())),
                Box::new(PLTL::Globally(lhs.clone())),
            )),
            PLTL::WeakSince(lhs, rhs) => self.models(&PLTL::Or(
                Box::new(PLTL::Since(lhs.clone(), rhs.clone())),
                Box::new(PLTL::Historically(lhs.clone())),
            )),
            PLTL::Release(lhs, rhs) => self.models(&PLTL::WeakUntil(
                rhs.clone(),
                Box::new(PLTL::And(lhs.clone(), rhs.clone())),
            )),
            PLTL::WeakBefore(lhs, rhs) => self.models(&PLTL::WeakSince(
                rhs.clone(),
                Box::new(PLTL::And(lhs.clone(), rhs.clone())),
            )),
            PLTL::WeakYesterday(pltl) => self.models(&PLTL::Or(
                Box::new(PLTL::Yesterday(pltl.clone())),
                Box::new(PLTL::Not(Box::new(PLTL::Yesterday(Box::new(PLTL::Top))))),
            )),
        }
    }
}
