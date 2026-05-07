from flask import Flask, render_template, request, jsonify, redirect, url_for, flash, session
from flask_sqlalchemy import SQLAlchemy
from flask_login import LoginManager, UserMixin, login_user, logout_user, current_user, login_required
from werkzeug.security import generate_password_hash, check_password_hash
import random
import math
from datetime import datetime, timedelta
import os
import re  # for parsing numbers in chatbot


app = Flask(__name__)
app.config["SECRET_KEY"] = os.environ.get("SECRET_KEY", "dev-secret-key-change-in-production")
app.config["SQLALCHEMY_DATABASE_URI"] = os.environ.get("DATABASE_URL", "sqlite:///Numerography.db")
app.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False
app.config["REMEMBER_COOKIE_DURATION"] = timedelta(days=30)

# Initialize extensions
db = SQLAlchemy(app)
login_manager = LoginManager(app)
login_manager.login_view = "login"
login_manager.login_message = "Please log in to access this feature."

# ========================================
# DATABASE MODELS
# ========================================
class User(db.Model, UserMixin):
    __tablename__ = "users"
    id = db.Column(db.Integer, primary_key=True)
    username = db.Column(db.String(80), unique=True, nullable=False)
    email = db.Column(db.String(120), unique=True, nullable=True)
    password_hash = db.Column(db.String(200), nullable=False)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    calculations = db.relationship("Calculation", backref="user", lazy=True, cascade="all, delete-orphan")
    
    def set_password(self, password):
        self.password_hash = generate_password_hash(password)
    
    def verify_password(self, password):
        return check_password_hash(self.password_hash, password)

class Calculation(db.Model):
    __tablename__ = "calculations"
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("users.id"), nullable=True)
    operation_type = db.Column(db.String(50), nullable=False)
    input_values = db.Column(db.Text, nullable=False)
    output_result = db.Column(db.Text, nullable=False)
    notes = db.Column(db.Text, nullable=True)
    is_starred = db.Column(db.Boolean, default=False)
    computed_at = db.Column(db.DateTime, default=datetime.utcnow)

@login_manager.user_loader
def load_user(user_id):
    return User.query.get(int(user_id))

# ========================================
# MATHEMATICAL FUNCTIONS
# ========================================

def decompose_into_primes(number):
    """Breaks down a number into its prime factors with exponents."""
    if number < 2:
        return {}
    
    prime_powers = {}
    
    # Handle factor of 2
    while number % 2 == 0:
        prime_powers[2] = prime_powers.get(2, 0) + 1
        number //= 2
    
    # Check odd factors
    divisor = 3
    while divisor * divisor <= number:
        while number % divisor == 0:
            prime_powers[divisor] = prime_powers.get(divisor, 0) + 1
            number //= divisor
        divisor += 2
    
    # If number > 1, then it's a prime factor
    if number > 1:
        prime_powers[number] = prime_powers.get(number, 0) + 1
    
    return prime_powers

def compute_phi_function(number):
    """Calculates Euler's totient function φ(n)."""
    if number < 1:
        return 0
    if number == 1:
        return 1
    
    prime_factors = decompose_into_primes(number)
    phi_value = number
    
    for prime in prime_factors:
        phi_value -= phi_value // prime
    
    return phi_value

def probabilistic_primality_test(number, rounds=10):
    """Miller-Rabin probabilistic primality test."""
    if number < 2:
        return False
    if number == 2 or number == 3:
        return True
    if number % 2 == 0:
        return False
    
    # Small prime check
    small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    for p in small_primes:
        if number == p:
            return True
        if number % p == 0:
            return False
    
    # Write n-1 as 2^r * d
    r, d = 0, number - 1
    while d % 2 == 0:
        d //= 2
        r += 1
    
    def witness_test(a, s, d, n):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            return True
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                return True
        return False
    
    for _ in range(rounds):
        witness = random.randrange(2, number - 1)
        if not witness_test(witness, r, d, number):
            return False
    
    return True

def modular_power(base, exponent, modulus=None):
    """Efficient exponentiation with optional modulus."""
    if modulus:
        return pow(base, exponent, modulus)
    return base ** exponent

def extended_euclidean(a, b):
    """Returns gcd, and coefficients x, y such that ax + by = gcd(a,b)."""
    if a == 0:
        return b, 0, 1
    
    gcd_val, x1, y1 = extended_euclidean(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    
    return gcd_val, x, y

def find_modular_inverse(a, m):
    """Finds the modular inverse of a mod m."""
    gcd_val, x, _ = extended_euclidean(a, m)
    
    if gcd_val != 1:
        return None  # Modular inverse doesn't exist
    
    return (x % m + m) % m

def solve_congruence_system(remainders, moduli):
    """Solves a system of congruences using Chinese Remainder Theorem."""
    if len(remainders) != len(moduli):
        raise ValueError("Remainders and moduli lists must have the same length")
    
    total_product = 1
    for m in moduli:
        total_product *= m
    
    solution = 0
    for remainder, modulus in zip(remainders, moduli):
        partial_product = total_product // modulus
        inverse = find_modular_inverse(partial_product, modulus)
        solution += remainder * partial_product * inverse
    
    return solution % total_product

def compute_gcd(a, b):
    """Computes the greatest common divisor using Euclidean algorithm."""
    while b:
        a, b = b, a % b
    return a

def compute_lcm(a, b):
    """Computes the least common multiple."""
    return abs(a * b) // compute_gcd(a, b)

# ========================================
# FORMATTING HELPER FUNCTIONS
# ========================================

def to_superscript(n):
    """Convert number to superscript unicode."""
    superscripts = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")
    return str(n).translate(superscripts)

def format_factorization_for_display(n, factors):
    """Format factorization as: 60 = 2² × 3 × 5"""
    if not factors:
        return f"{n} = 1"
    
    parts = []
    for prime in sorted(factors.keys()):
        exp = factors[prime]
        if exp == 1:
            parts.append(str(prime))
        else:
            parts.append(f"{prime}{to_superscript(exp)}")
    
    return f"{n} = {' × '.join(parts)}"

def format_modular_exp_for_display(base, exp, mod, result):
    """Format modular exponentiation as: 3¹⁰⁰ ≡ 4 (mod 7)"""
    return f"{base}{to_superscript(exp)} ≡ {result} (mod {mod})"

def format_crt_for_display(remainders, moduli, solution):
    """Format CRT solution as: x ≡ 11 (mod 60)"""
    product = math.prod(moduli)
    return f"x ≡ {solution} (mod {product})"

def format_gcd_lcm_for_display(a, b, gcd_val, lcm_val):
    """Format GCD/LCM as: GCD(48, 18) = 6, LCM(48, 18) = 144"""
    return f"GCD({a}, {b}) = {gcd_val}, LCM({a}, {b}) = {lcm_val}"

def format_primality_for_display(n, is_prime):
    """Format primality result as: 7 is PRIME or 33 is COMPOSITE"""
    return f"{n} is {'PRIME' if is_prime else 'COMPOSITE'}"

def format_euler_phi_for_display(n, phi):
    """Format Euler's totient as: φ(100) = 40"""
    return f"φ({n}) = {phi}"

# ========================================
# CHATBOT EXPLANATION HELPERS (STEP-BY-STEP)
# ========================================

def explain_factorization(n):
    factors = decompose_into_primes(n)
    result_line = format_factorization_for_display(n, factors)

    lines = [f"We factor {n} by dividing by small primes:"]

    temp = n
    for p in sorted(factors.keys()):
        count = factors[p]
        for _ in range(count):
            new_temp = temp // p
            lines.append(f"• Divide by {p}: {temp} ÷ {p} = {new_temp} (remainder 0)")
            temp = new_temp

    parts = [f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(factors.items())]
    lines.append("")
    lines.append(f"So {n} = " + " × ".join(parts) + ".")

    explanation = "\n".join(lines)
    return result_line, explanation


def explain_euler_phi(n):
    phi_val = compute_phi_function(n)
    result_line = format_euler_phi_for_display(n, phi_val)

    factors = decompose_into_primes(n)
    lines = [f"First factor {n}:", ""]
    parts = [f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(factors.items())]
    lines.append("  " + f"{n} = " + " × ".join(parts))

    lines.append("")
    lines.append("Euler's totient uses the formula:")
    lines.append("  φ(n) = n × Π (1 − 1/p) over distinct prime factors p.")
    lines.append("")
    phi_step = float(n)
    for p in sorted(factors.keys()):
        lines.append(f"• Multiply by (1 − 1/{p}) = (1 − 1/{p})")
        phi_step *= (1 - 1 / p)
        lines.append(f"  Intermediate value ≈ {phi_step:.2f}")

    lines.append("")
    lines.append(f"Rounding to an integer gives φ({n}) = {phi_val}.")
    explanation = "\n".join(lines)
    return result_line, explanation


def explain_primality(n, rounds):
    is_prime = probabilistic_primality_test(n, rounds)
    result_line = format_primality_for_display(n, is_prime)

    lines = [f"We test whether {n} is prime using a Miller–Rabin style test:"]

    if n < 2:
        lines.append("• Any number < 2 is not prime.")
    elif n in (2, 3):
        lines.append("• 2 and 3 are prime by definition.")
    elif n % 2 == 0:
        lines.append("• Even numbers > 2 are not prime.")
    else:
        lines.append("1) Check divisibility by small primes (3, 5, 7, 11, ...).")
        lines.append("2) Write n − 1 as 2^r · d with d odd.")
        lines.append("3) For several random bases a, compute a^d mod n,")
        lines.append("   then repeatedly square to see if we ever hit 1 or n − 1.")
        lines.append("   If a base proves n composite, we stop.")

    lines.append("")
    lines.append(f"After {rounds} rounds, we conclude {result_line}.")
    explanation = "\n".join(lines)
    return result_line, explanation


def explain_modexp(base, exp, mod):
    original_base, original_exp = base, exp
    result = 1
    base = base % mod
    e = exp
    step = 1
    lines = [f"We compute {original_base}^{original_exp} mod {mod} using repeated squaring:", ""]

    while e > 0:
        lines.append(f"Step {step}: exponent = {e}")
        if e % 2 == 1:
            new_result = (result * base) % mod
            lines.append(f"  • exponent is odd → multiply result:")
            lines.append(f"    result = ({result} × {base}) mod {mod} = {new_result}")
            result = new_result
        new_base = (base * base) % mod
        lines.append(f"  • square base: base = ({base}²) mod {mod} = {new_base}")
        base = new_base
        e //= 2
        lines.append("")
        step += 1

    lines.append(f"Final answer: {original_base}^{original_exp} ≡ {result} (mod {mod}).")
    explanation = "\n".join(lines)
    result_line = format_modular_exp_for_display(original_base, original_exp, mod, result)
    return result_line, explanation


def explain_gcd_lcm(a, b):
    gcd_val = compute_gcd(a, b)
    lcm_val = compute_lcm(a, b)
    result_line = format_gcd_lcm_for_display(a, b, gcd_val, lcm_val)

    x, y = a, b
    lines = [f"We find gcd({a}, {b}) using the Euclidean algorithm:", ""]
    step = 1
    while y != 0:
        q = x // y
        r = x % y
        lines.append(f"Step {step}: {x} = {y} × {q} + {r}")
        x, y = y, r
        step += 1

    lines.append("")
    lines.append(f"The last non-zero remainder is {x}, so gcd({a}, {b}) = {x}.")
    if gcd_val != 0:
        lines.append("")
        lines.append("The LCM is given by:")
        lines.append(f"  lcm(a, b) = |a × b| / gcd(a, b)")
        lines.append(f"  lcm({a}, {b}) = |{a} × {b}| / {gcd_val} = {lcm_val}")
    explanation = "\n".join(lines)
    return result_line, explanation


def explain_crt(remainders, moduli):
    solution = solve_congruence_system(remainders, moduli)
    result_line = format_crt_for_display(remainders, moduli, solution)

    N = math.prod(moduli)
    lines = [
        "We solve the system using the Chinese Remainder Theorem:",
        "",
        f"Total modulus N = m₁ × m₂ × ... = {N}",
        ""
    ]

    for i, (r, m) in enumerate(zip(remainders, moduli), start=1):
        Mi = N // m
        yi = find_modular_inverse(Mi, m)
        term = r * Mi * yi
        lines.append(f"Equation {i}: x ≡ {r} (mod {m})")
        lines.append(f"  • M{i} = N / {m} = {Mi}")
        lines.append(f"  • y{i} = inverse(M{i} mod {m}) = {yi}")
        lines.append(f"  • contribution = {r} × {Mi} × {yi} = {term}")
        lines.append("")

    lines.append("Sum of contributions S = Σ rᵢ Mᵢ yᵢ.")
    lines.append(f"Then x ≡ S mod N, which gives x ≡ {solution} (mod {N}).")
    explanation = "\n".join(lines)
    return result_line, explanation


# ========================================
# HELPER FUNCTIONS (HISTORY, FORMATTING)
# ========================================

def record_calculation(operation, inputs, result):
    """Records a calculation to database or session."""
    if current_user.is_authenticated:
        calc = Calculation(
            user_id=current_user.id,
            operation_type=operation,
            input_values=str(inputs),
            output_result=result
        )
        db.session.add(calc)
        db.session.commit()
    else:
        # Store in session for anonymous users
        session_key = f"calc_{operation}"
        history = session.get(session_key, [])
        history.append({
            "inputs": str(inputs),
            "result": result,
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        })
        session[session_key] = history[-15:]  # Keep last 15

def fetch_calculation_history(operation):
    """Retrieves calculation history with formatted display."""
    if current_user.is_authenticated:
        calcs = Calculation.query.filter_by(
            user_id=current_user.id,
            operation_type=operation
        ).order_by(Calculation.computed_at.desc()).limit(15).all()
        
        return [{
            "id": c.id,
            "inputs": format_inputs_for_display(operation, c.input_values),
            "result": c.output_result,
            "timestamp": c.computed_at.strftime("%Y-%m-%d %H:%M:%S"),
            "starred": c.is_starred
        } for c in calcs]
    else:
        session_key = f"calc_{operation}"
        history = session.get(session_key, [])
        
        # Format inputs for display
        formatted_history = []
        for item in history:
            formatted_item = item.copy()
            formatted_item["inputs"] = format_inputs_for_display(operation, item["inputs"])
            formatted_history.append(formatted_item)
        
        return formatted_history

def format_inputs_for_display(operation, inputs_str):
    """Format input string into readable format."""
    try:
        # Parse the input string safely
        inputs_dict = eval(inputs_str)
        
        if operation == "factorization":
            return f"{inputs_dict.get('n', 'N/A')}"
        
        elif operation == "euler_phi":
            return f"{inputs_dict.get('n', 'N/A')}"
        
        elif operation == "primality":
            n = inputs_dict.get('n', 'N/A')
            return f"{n}"
        
        elif operation == "mod_exp":
            base = inputs_dict.get('base', 'N/A')
            exp = inputs_dict.get('exp', 'N/A')
            mod = inputs_dict.get('mod', 'N/A')
            return f"{base}{to_superscript(exp)} mod {mod}"
        
        elif operation == "crt":
            if 'remainders' in inputs_dict:
                remainders = inputs_dict.get('remainders', [])
                moduli = inputs_dict.get('moduli', [])
                # Format as system of congruences
                parts = [f"x ≡ {r} (mod {m})" for r, m in zip(remainders, moduli)]
                return ", ".join(parts)
            else:
                number = inputs_dict.get('number', 'N/A')
                moduli = inputs_dict.get('moduli', [])
                return f"{number} mod {moduli}"
        
        elif operation == "gcd_lcm":
            a = inputs_dict.get('a', 'N/A')
            b = inputs_dict.get('b', 'N/A')
            return f"{a}, {b}"
        
        elif operation == "mod_inverse":
            a = inputs_dict.get('a', 'N/A')
            m = inputs_dict.get('m', 'N/A')
            return f"{a} mod {m}"
        
        else:
            return inputs_str
            
    except:
        # If parsing fails, return original string
        return inputs_str

# ========================================
# CHATBOT EXPLANATION HELPERS (CONCEPTUAL)
# ========================================

def explain_factorization_concept():
    return (
        "🔍 Prime factorization:\n"
        "- We repeatedly divide your number by the smallest prime that still divides it.\n"
        "- First we strip off all factors of 2.\n"
        "- Then we try odd numbers 3, 5, 7, ... up to √n.\n"
        "- Every time a divisor works, we count how many times it divides n.\n"
        "- The final answer is written as a product of primes with exponents, e.g. 60 = 2² × 3 × 5."
    )

def explain_euler_phi_concept():
    return (
        "φ(n) – Euler's Totient:\n"
        "- Step 1: Factor n into primes: n = p₁^{e₁} · p₂^{e₂} · ...\n"
        "- Step 2: Apply the formula φ(n) = n · Π(1 - 1/pᵢ) over all prime factors pᵢ.\n"
        "- This counts how many numbers between 1 and n are coprime with n.\n"
        "- Example: n = 12 = 2² · 3 → φ(12) = 12 · (1 - 1/2) · (1 - 1/3) = 12 · 1/2 · 2/3 = 4."
    )

def explain_primality_concept():
    return (
        "Miller–Rabin primality test (used in the app):\n"
        "- Write n − 1 as 2ʳ · d with d odd.\n"
        "- Randomly pick a base a between 2 and n−2.\n"
        "- Compute x = aᵈ mod n.\n"
        "- If x is 1 or n − 1, this round passes.\n"
        "- Otherwise we square x repeatedly (r−1 times): x ← x² mod n.\n"
        "- If we ever hit n − 1, the round passes; otherwise n is definitely composite.\n"
        "- If many rounds pass, n is *very likely* prime."
    )

def explain_mod_exp_concept():
    return (
        "Modular exponentiation (square-and-multiply):\n"
        "- We want base^exp mod m without computing the huge power directly.\n"
        "- Write the exponent in binary.\n"
        "- Scan bits from left to right:\n"
        "  · Square the current value each step (mod m).\n"
        "  · When a bit is 1, also multiply by the base (mod m).\n"
        "- This reduces the number of multiplications from ~exp to about log₂(exp)."
    )

def explain_gcd_lcm_concept():
    return (
        "GCD & LCM in the app:\n"
        "- GCD(a, b) is computed with the Euclidean algorithm:\n"
        "  · Repeatedly replace (a, b) by (b, a mod b) until b = 0.\n"
        "  · The last non-zero a is gcd(a, b).\n"
        "- LCM(a, b) then uses the identity: a · b = GCD(a, b) · LCM(a, b).\n"
        "- So LCM(a, b) = |a · b| / GCD(a, b)."
    )

def explain_crt_concept():
    return (
        "Chinese Remainder Theorem (CRT) in the app:\n"
        "- Suppose you give congruences x ≡ rᵢ (mod mᵢ) with pairwise coprime moduli.\n"
        "- Step 1: Compute M = product of all moduli.\n"
        "- Step 2: For each i, let Mᵢ = M / mᵢ.\n"
        "- Step 3: Find the modular inverse yᵢ of Mᵢ modulo mᵢ so that Mᵢ · yᵢ ≡ 1 (mod mᵢ).\n"
        "- Step 4: Combine: x ≡ Σ rᵢ · Mᵢ · yᵢ  (mod M).\n"
        "- The app follows exactly this recipe."
    )

def default_chatbot_help():
    return (
        "Hi! I’m the Numerography tutor 🤖.\n"
        "You can ask me to *do* a calculation or to *explain* one.\n\n"
        "Try things like:\n"
        "• \"Do CRT with me\" (I’ll ask for remainders and moduli)\n"
        "• \"Compute GCD\" or \"gcd 48 18\"\n"
        "• \"Factor a number\"\n"
        "• \"Explain modular exponentiation\""
    )

def answer_chatbot_question(message: str) -> str:
    """Conceptual explanations for 'explain' / 'how' style questions."""
    text = (message or "").lower()

    if "crt" in text or "chinese remainder" in text:
        return explain_crt_concept()
    if "gcd" in text or "lcm" in text or "greatest common" in text:
        return explain_gcd_lcm_concept()
    if "mod" in text and ("power" in text or "exponent" in text or "exponentiation" in text):
        return explain_mod_exp_concept()
    if "prime" in text and ("test" in text or "miller" in text or "rabin" in text):
        return explain_primality_concept()
    if "totient" in text or "phi" in text or "φ(" in text or "euler" in text:
        return explain_euler_phi_concept()
    if "factor" in text or "prime factor" in text:
        return explain_factorization_concept()

    return default_chatbot_help()

# ========================================
# ROUTES
# ========================================

@app.route("/")
@login_required
def index():
    return render_template("index.html")

@app.route("/register", methods=["GET", "POST"])
def register():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        email = request.form.get("email", "").strip()
        password = request.form.get("password", "")
        
        if not username or not password:
            flash("Username and password are required.", "error")
            return redirect(url_for("register"))
        
        if User.query.filter_by(username=username).first():
            flash("Username already taken. Please choose another.", "error")
            return redirect(url_for("register"))
        
        new_user = User(username=username, email=email if email else None)
        new_user.set_password(password)
        db.session.add(new_user)
        db.session.commit()
        
        login_user(new_user)
        flash("Registration successful! Welcome to Numerography.", "success")
        return redirect(url_for("index"))
    
    return render_template("register.html")

@app.route("/login", methods=["GET", "POST"])
def login():
    if current_user.is_authenticated:
        return redirect(url_for("index"))
    
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        password = request.form.get("password", "").strip()
        
        user = User.query.filter_by(username=username).first()
        
        if user and user.verify_password(password):
            remember = bool(request.form.get("remember"))
            login_user(user, remember=remember)
            flash(f"Welcome back, {username}!", "success")
            next_page = request.args.get("next")
            return redirect(next_page if next_page else url_for("index"))
        else:
            flash("Invalid username or password.", "error")
    
    return render_template("login.html")

@app.route("/logout")
@login_required
def logout():
    logout_user()
    flash("You've been logged out successfully.", "info")
    return redirect(url_for("login"))

@app.route("/factorization")
def factorization():
    history = fetch_calculation_history("factorization")
    return render_template("factorization.html", history=history)

@app.route("/euler-phi")
def euler_phi():
    history = fetch_calculation_history("euler_phi")
    return render_template("euler_phi.html", history=history)

@app.route("/primality-test")
def primality_test():
    history = fetch_calculation_history("primality")
    return render_template("primality.html", history=history)

@app.route("/modular-exponentiation")
def modular_exponentiation():
    history = fetch_calculation_history("mod_exp")
    return render_template("modular_exp.html", history=history)

@app.route("/chinese-remainder")
def chinese_remainder():
    history = fetch_calculation_history("crt")
    return render_template("crt.html", history=history)

@app.route("/gcd-lcm")
def gcd_lcm():
    history = fetch_calculation_history("gcd_lcm")
    return render_template("gcd_lcm.html", history=history)

@app.route("/modular-inverse")
def modular_inverse():
    history = fetch_calculation_history("mod_inverse")
    return render_template("mod_inverse.html", history=history)

@app.route("/calculate", methods=["POST"])
def calculate():
    """Unified calculation endpoint."""
    data = request.get_json()
    operation = data.get("operation")
    result_text = ""
    
    try:
        if operation == "factorization":
            n = int(data["number"])
            factors = decompose_into_primes(n)
            result_text = format_factorization_for_display(n, factors)
            record_calculation("factorization", {"n": n}, result_text)
            
        elif operation == "euler_phi":
            n = int(data["number"])
            phi = compute_phi_function(n)
            result_text = format_euler_phi_for_display(n, phi)
            record_calculation("euler_phi", {"n": n}, result_text)
            
        elif operation == "primality":
            n = int(data["number"])
            rounds = int(data.get("rounds", 10))
            is_prime = probabilistic_primality_test(n, rounds)
            result_text = format_primality_for_display(n, is_prime)
            record_calculation("primality", {"n": n, "rounds": rounds}, result_text)
            
        elif operation == "mod_exp":
            base = int(data["base"])
            exp = int(data["exponent"])
            mod = int(data["modulus"])
            
            result = modular_power(base, exp, mod)
            result_text = format_modular_exp_for_display(base, exp, mod, result)
            record_calculation("mod_exp", {"base": base, "exp": exp, "mod": mod}, result_text)
            
        elif operation == "crt":
            remainders = list(map(int, data["remainders"].split(",")))
            moduli = list(map(int, data["moduli"].split(",")))
            solution = solve_congruence_system(remainders, moduli)
            result_text = format_crt_for_display(remainders, moduli, solution)
            record_calculation("crt", {"remainders": remainders, "moduli": moduli}, result_text)
                
        elif operation == "gcd_lcm":
            a = int(data["a"])
            b = int(data["b"])
            gcd_val = compute_gcd(a, b)
            lcm_val = compute_lcm(a, b)
            result_text = format_gcd_lcm_for_display(a, b, gcd_val, lcm_val)
            record_calculation("gcd_lcm", {"a": a, "b": b}, result_text)
            
        elif operation == "mod_inverse":
            a = int(data["a"])
            m = int(data["m"])
            inverse = find_modular_inverse(a, m)
            
            if inverse is not None:
                result_text = f"Modular inverse of {a} mod {m} = {inverse}"
            else:
                result_text = f"Modular inverse does not exist (gcd({a}, {m}) ≠ 1)"
            
            record_calculation("mod_inverse", {"a": a, "m": m}, result_text)
            
        return jsonify({"success": True, "result": result_text})
        
    except Exception as e:
        return jsonify({"success": False, "result": f"Error: {str(e)}"})

@app.route("/api/chatbot", methods=["POST"])
def chatbot_api():
    """
    Interactive educational chatbot for number theory.
    Uses session['chat_state'] to run multi-step flows (e.g. CRT).
    """
    data = request.get_json() or {}
    message = (data.get("message") or "").strip()

    if not message:
        return jsonify({
            "success": False,
            "reply": "Please type a question or say what you want to compute."
        })

    text = message.lower()
    state = session.get("chat_state", {"mode": "idle"})

    # Global reset / cancel
    if text in {"cancel", "reset", "stop"}:
        session["chat_state"] = {"mode": "idle"}
        return jsonify({"success": True, "reply": "Okay, I reset the conversation. What would you like to do next?"})

    # Helper to parse ints
    def parse_ints(msg):
        return [int(x) for x in re.findall(r"-?\d+", msg)]

    # -------------------------
    # Handle ongoing flows
    # -------------------------
    mode = state.get("mode", "idle")

    # CRT: waiting for remainders
    if mode == "crt_wait_remainders":
        remainders = parse_ints(message)
        if not remainders:
            reply = "I didn't see any integers. Please send the remainders separated by commas, e.g. 2, 3, 1."
            return jsonify({"success": True, "reply": reply})
        state["remainders"] = remainders
        state["mode"] = "crt_wait_moduli"
        session["chat_state"] = state
        reply = (
            f"Great, remainders r = {remainders}.\n"
            "Now send the **moduli** (same count) separated by commas, e.g. 5, 7, 9."
        )
        return jsonify({"success": True, "reply": reply})

    # CRT: waiting for moduli
    if mode == "crt_wait_moduli":
        moduli = parse_ints(message)
        remainders = state.get("remainders", [])
        if not moduli:
            reply = "I didn't see any integers. Please send the moduli separated by commas, e.g. 5, 7, 9."
            return jsonify({"success": True, "reply": reply})
        if len(moduli) != len(remainders):
            reply = (
                f"You gave {len(remainders)} remainders but {len(moduli)} moduli.\n"
                "Please send the moduli again with the **same count** as the remainders."
            )
            return jsonify({"success": True, "reply": reply})
        try:
            result_line, explanation = explain_crt(remainders, moduli)
            record_calculation("crt", {"remainders": remainders, "moduli": moduli}, result_line)
            reply = result_line + "\n\nExplanation:\n" + explanation
        except Exception as e:
            reply = f"Error while solving the CRT system: {e}"
        session["chat_state"] = {"mode": "idle"}
        return jsonify({"success": True, "reply": reply})

    # GCD/LCM interactive
    if mode == "gcd_wait_numbers":
        nums = parse_ints(message)
        if len(nums) < 2:
            return jsonify({"success": True, "reply": "Please send two integers, e.g. 48, 18."})
        a, b = nums[0], nums[1]
        result_line, explanation = explain_gcd_lcm(a, b)
        record_calculation("gcd_lcm", {"a": a, "b": b}, result_line)
        session["chat_state"] = {"mode": "idle"}
        reply = result_line + "\n\nExplanation:\n" + explanation
        return jsonify({"success": True, "reply": reply})

    # Factorization interactive
    if mode == "factor_wait_n":
        nums = parse_ints(message)
        if not nums:
            return jsonify({"success": True, "reply": "Please send a single integer to factor, e.g. 84."})
        n = nums[0]
        result_line, explanation = explain_factorization(n)
        record_calculation("factorization", {"n": n}, result_line)
        session["chat_state"] = {"mode": "idle"}
        reply = result_line + "\n\nExplanation:\n" + explanation
        return jsonify({"success": True, "reply": reply})

    # φ(n) interactive
    if mode == "phi_wait_n":
        nums = parse_ints(message)
        if not nums:
            return jsonify({"success": True, "reply": "Please send an integer n, e.g. 100."})
        n = nums[0]
        result_line, explanation = explain_euler_phi(n)
        record_calculation("euler_phi", {"n": n}, result_line)
        session["chat_state"] = {"mode": "idle"}
        reply = result_line + "\n\nExplanation:\n" + explanation
        return jsonify({"success": True, "reply": reply})

    # Primality interactive
    if mode == "prime_wait_n":
        nums = parse_ints(message)
        if not nums:
            return jsonify({"success": True, "reply": "Please send an integer n, e.g. 97."})
        n = nums[0]
        rounds = 10
        result_line, explanation = explain_primality(n, rounds)
        record_calculation("primality", {"n": n, "rounds": rounds}, result_line)
        session["chat_state"] = {"mode": "idle"}
        reply = result_line + "\n\nExplanation:\n" + explanation
        return jsonify({"success": True, "reply": reply})

    # Modular exponentiation interactive
    if mode == "modexp_wait_numbers":
        nums = parse_ints(message)
        if len(nums) < 3:
            return jsonify({"success": True, "reply": "Please send base, exponent, modulus, e.g. 2, 10, 7."})
        base, exp, mod = nums[0], nums[1], nums[2]
        result_line, explanation = explain_modexp(base, exp, mod)
        record_calculation("mod_exp", {"base": base, "exp": exp, "mod": mod}, result_line)
        session["chat_state"] = {"mode": "idle"}
        reply = result_line + "\n\nExplanation:\n" + explanation
        return jsonify({"success": True, "reply": reply})

    # -------------------------
    # No active flow → detect intent
    # -------------------------
    nums = parse_ints(message)

    # CRT: start interactive flow
    if "crt" in text or "chinese remainder" in text:
        session["chat_state"] = {"mode": "crt_wait_remainders"}
        reply = (
            "Great, let's solve a CRT system together!\n"
            "First, send the **remainders** separated by commas, e.g. 2, 3, 1."
        )
        return jsonify({"success": True, "reply": reply})

    # GCD/LCM
    if "gcd" in text or "lcm" in text or "greatest common" in text:
        if len(nums) >= 2:
            a, b = nums[0], nums[1]
            result_line, explanation = explain_gcd_lcm(a, b)
            record_calculation("gcd_lcm", {"a": a, "b": b}, result_line)
            reply = result_line + "\n\nExplanation:\n" + explanation
            return jsonify({"success": True, "reply": reply})
        else:
            session["chat_state"] = {"mode": "gcd_wait_numbers"}
            reply = "Sure! Send the two integers a and b separated by a comma, e.g. 48, 18."
            return jsonify({"success": True, "reply": reply})

    # Prime factorization
    if "factor" in text or "prime factor" in text:
        if nums:
            n = nums[0]
            result_line, explanation = explain_factorization(n)
            record_calculation("factorization", {"n": n}, result_line)
            reply = result_line + "\n\nExplanation:\n" + explanation
            return jsonify({"success": True, "reply": reply})
        else:
            session["chat_state"] = {"mode": "factor_wait_n"}
            reply = "Tell me the integer you want to factor, e.g. 84."
            return jsonify({"success": True, "reply": reply})

    # Euler φ(n)
    if "totient" in text or "phi" in text or "φ(" in text or "euler" in text:
        if nums:
            n = nums[0]
            result_line, explanation = explain_euler_phi(n)
            record_calculation("euler_phi", {"n": n}, result_line)
            reply = result_line + "\n\nExplanation:\n" + explanation
            return jsonify({"success": True, "reply": reply})
        else:
            session["chat_state"] = {"mode": "phi_wait_n"}
            reply = "Sure! Send me n so I can compute φ(n), e.g. 100."
            return jsonify({"success": True, "reply": reply})

    # Primality
    if "prime" in text and ("check" in text or "test" in text or "is" in text or "?" in text):
        if nums:
            n = nums[0]
            rounds = 10
            result_line, explanation = explain_primality(n, rounds)
            record_calculation("primality", {"n": n, "rounds": rounds}, result_line)
            reply = result_line + "\n\nExplanation:\n" + explanation
            return jsonify({"success": True, "reply": reply})
        else:
            session["chat_state"] = {"mode": "prime_wait_n"}
            reply = "Which number do you want to test for primality?"
            return jsonify({"success": True, "reply": reply})

    # Modular exponentiation
    if "modexp" in text or "mod exp" in text or ("mod" in text and "^" in text):
        if len(nums) >= 3:
            base, exp, mod = nums[0], nums[1], nums[2]
            result_line, explanation = explain_modexp(base, exp, mod)
            record_calculation("mod_exp", {"base": base, "exp": exp, "mod": mod}, result_line)
            reply = result_line + "\n\nExplanation:\n" + explanation
            return jsonify({"success": True, "reply": reply})
        else:
            session["chat_state"] = {"mode": "modexp_wait_numbers"}
            reply = "Send base, exponent, and modulus separated by commas, e.g. 2, 10, 7."
            return jsonify({"success": True, "reply": reply})

    # Pure explanation questions ("explain", "how", etc.)
    if "explain" in text or "how" in text:
        reply = answer_chatbot_question(message)
        return jsonify({"success": True, "reply": reply})

    # Fallback help
    reply = default_chatbot_help()
    return jsonify({"success": True, "reply": reply})

@app.route("/clear-history/<operation>", methods=["POST"])
@login_required
def clear_history(operation):
    """Clear calculation history for a specific operation."""
    try:
        Calculation.query.filter_by(
            user_id=current_user.id,
            operation_type=operation
        ).delete()
        db.session.commit()
        return jsonify({"success": True})
    except Exception as e:
        return jsonify({"success": False, "error": str(e)})

@app.route("/profile")
@login_required
def profile():
    recent_calcs = Calculation.query.filter_by(
        user_id=current_user.id
    ).order_by(Calculation.computed_at.desc()).limit(20).all()
    
    # Format the calculations for display
    formatted_calcs = []
    for calc in recent_calcs:
        formatted_calc = {
            'id': calc.id,
            'operation_type': calc.operation_type,
            'input_values': format_inputs_for_display(calc.operation_type, calc.input_values),
            'output_result': calc.output_result,
            'computed_at': calc.computed_at
        }
        formatted_calcs.append(formatted_calc)
    
    return render_template("profile.html", calculations=formatted_calcs)

# ========================================
# MAIN
# ========================================
if __name__ == "__main__":
    with app.app_context():
        db.create_all()
    app.run(debug=False, port=5000, use_reloader=False)
