"""Optional shared per-run completion-token ceiling, including API retries."""
from threading import Condition


class OutputBudgetExhausted(RuntimeError):
    pass


class OutputBudget:
    def __init__(self, limit):
        if limit <= 0:
            raise ValueError('Output budget must be positive')
        self.limit = limit
        self.used = self.reserved = self.unreported = 0
        self.condition = Condition()

    def reserve(self, requested):
        with self.condition:
            while self.limit - self.used - self.reserved <= 0 and self.reserved:
                self.condition.wait(timeout=1)
            allocation = min(requested, self.limit - self.used - self.reserved)
            if allocation <= 0:
                raise OutputBudgetExhausted('Shared completion-token budget exhausted')
            self.reserved += allocation
            return allocation

    def release(self, allocation, consumed):
        with self.condition:
            self.reserved -= allocation
            # A missing response has unknown usage: conservatively charge its cap.
            self.used += allocation if consumed is None else consumed
            if consumed is None:
                self.unreported += allocation
            self.condition.notify_all()

    def snapshot(self):
        with self.condition:
            return {'limit': self.limit, 'consumed_or_conservatively_charged': self.used,
                    'reserved': self.reserved, 'unreported_charged': self.unreported}
